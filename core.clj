(ns cloj-test.core
  (:import (java.time LocalDateTime)
           (java.time.format DateTimeFormatter)))

(defrecord Registers [mem stack env code dump])

(defprotocol Instruction
  "General MSECD instruction"
  (execute [this state] "Execute a MSECD instruction")
  (instr-name [this] "Get name of this instruction"))

(defn set-regs
  [state regs]
  (assoc state :regs regs))

;; Put NIL into S
;; m s e (NIL.c) d -> m (nil.s) e c d
(defrecord i-nil [] Instruction
  (instr-name [_] "NIL")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj (-> regs :stack) nil)))]
      (set-regs state (fun regs)))))
(def NIL (i-nil.))

;; Duplicate the top value on stack
;; m (x.s) e (DUP.c) d -> m (x x.s) e c d
(defrecord i-dup [] Instruction
  (instr-name [_] "DUP")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj (:stack regs) (first (:stack regs)))))]
      (set-regs state (fun regs)))))
(def DUP (i-dup.))

;; Put next element from C into S
;; m s e (LDC x.c) d -> m (x.s) e c d
(defrecord i-ldc [] Instruction
  (instr-name [_] "LDC")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (-> regs :stack)
                                              (first (-> regs :code)))
                                     :code (pop (-> regs :code))))]
      (set-regs state (fun regs)))))
(def LDC (i-ldc.))

(defn env-get [y x e]
  (nth (nth e y) x))

;; Put value from E into S
;; m s e (LD y x.c) d -> (env-get(y x e).s) e c d
(defrecord i-ld [] Instruction
  (instr-name [_] "LD")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (-> regs :stack)
                                              (env-get
                                                (first (-> regs :code))
                                                (second (-> regs :code))
                                                (-> regs :env)))
                                     :code (pop (pop (-> regs :code)))))]
      (set-regs state (fun regs)))))
(def LD (i-ld.))

(defn mem-get "Gets current variable value from M register.
Register structure: [(X (xt (Ct xt) (Cs xs).h)).m].
X - variable name,
xt - current value of X,
(Ct xt) - history entry,
Ct - thread name,
xt - value set by thread,
h - rest of history consists of such pairs in order of assigment,
m - rest of M (memory) consists of such variable structures in order of declaration."
  [mem name]                            ;; var in mem: (name (val.hist))
  (some #(if (= name (first %))         ;; if name is equal
           (first (second %)))          ;; return top element of value list
        mem))

(defn mem-contains "Returns nil if M register does not contain variable entry for name \"name\"."
  [mem name]
  (some #(= name (first %)) mem))

(defn mem-set "Sets new value to variable \"name\" from M register.
If it does not exist, new var entry is added to M.
Returns new M."
  [mem name val changer-name]
  (if (mem-contains mem name)
    (map #(if (= name (first %))
            (let [history (rest (second %))
                  new-hist-entry (list changer-name val)]
              (list name (conj history new-hist-entry val)))
            %)
         mem)
    (conj mem (list name (list val (list changer-name val))))))

;; Put current value of a variable in M by name from C into S
;; [(X (xt.Px)).m] s e (LDM X.c) d -> [(X (xt.Px)).m] (xt.s) e c d
(defrecord i-ldm [] Instruction
  (instr-name [_] "LDM")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (-> regs :stack)
                                              (mem-get @(-> regs :mem) (first (-> regs :code))))
                                     :code (pop (-> regs :code))))]
      (set-regs state (fun regs)))))
(def LDM (i-ldm.))

;; Put value from S to global var in M by name from C
;; [(X (x0.Px)).m] (xt.s) e (SET X.c) d -> [(X (xt Ct xt.Px)).m] s e c d
(defrecord i-set [] Instruction
  (instr-name [_] "SET")
  (execute [_ state]
    (let [regs (:regs state)
          changer-name (:id @*agent*)
          fun (fn [regs] (assoc regs :stack (pop (-> regs :stack))
                                     :code (pop (-> regs :code))))]
      (dosync
        (alter (:mem regs) mem-set
               (first (-> regs :code))
               (first (-> regs :stack))
               changer-name))
      (set-regs state (fun regs)))))
(def SET (i-set.))

;; Put function (instruction list) from C into S
;; m s e (LDF f.c) -> m ((f e).s) e c d
(defrecord i-ldf [] Instruction
  (instr-name [_] "LDF")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (-> regs :stack)
                                              (conj
                                                (-> regs :env)
                                                (first (-> regs :code))))
                                     :code (pop (-> regs :code))))]
      (set-regs state (fun regs)))))
(def LDF (i-ldf.))

;; Load function from S to C, dumping registers
;; m ((f e') v.s) e (AP.c) d -> m nil (v.e') f (s e c.d)
(defrecord i-ap [] Instruction
  (instr-name [_] "AP")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack nil
                                     :env (conj (second (first (-> regs :stack))) (second (-> regs :stack)))
                                     :code (first (first (-> regs :stack)))
                                     :dump (list (rest (pop (-> regs :stack))) (-> regs :env) (-> regs :code) (-> regs :dump))))]
      (set-regs state (fun regs)))))
(def AP (i-ap.))

;; Return control, restoring registers
;; m (x.s') e' (RTN.c') (s e c.d) -> m (x.s) e c d
(defrecord i-rtn [] Instruction
  (instr-name [_] "RTN")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj (first (-> regs :dump)) (first (-> regs :stack)))
                                     :env (second (-> regs :dump))
                                     :code (nth (-> regs :dump) 2)
                                     :dump (nth (-> regs :dump) 3)))]
      (set-regs state (fun regs)))))
(def RTN (i-rtn.))

;; Add two values from top of S, put result into S
;; m (x y.s) e (ADD.c) d -> m ((+ x y).s) e c d
(defrecord i-add [] Instruction
  (instr-name [_] "ADD")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (pop (pop (-> regs :stack)))
                                              (+ (first (-> regs :stack))
                                                 (second (-> regs :stack))))))]
      (set-regs state (fun regs)))))
(def ADD (i-add.))

;; Subtract two values from top of S, put result into S
;; m (x y.s) e (SUB.c) d -> m ((- x y).s) e c d
(defrecord i-sub [] Instruction
  (instr-name [_] "SUB")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (pop (pop (-> regs :stack)))
                                              (- (first (-> regs :stack))
                                                 (second (-> regs :stack))))))]
      (set-regs state (fun regs)))))
(def SUB (i-sub.))

;; Multiply two values from top of S, put result into S
;; m (x y.s) e (MUL.c) d -> m ((* x y).s) e c d
(defrecord i-mul [] Instruction
  (instr-name [_] "MUL")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (pop (pop (-> regs :stack)))
                                              (* (first (-> regs :stack))
                                                 (second (-> regs :stack))))))]
      (set-regs state (fun regs)))))
(def MUL (i-mul.))

;; Divide two values from top of S, put result into S
;; m (x y.s) e (DIV.c) d -> m ((/ x y).s) e c d
(defrecord i-div [] Instruction
  (instr-name [_] "DIV")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (pop (pop (-> regs :stack)))
                                              (/ (first (-> regs :stack))
                                                 (second (-> regs :stack))))))]
      (set-regs state (fun regs)))))
(def DIV (i-div.))

;; Check if two values on top of S are equal, put result into S
;; m (x y.s) e (EQ.c) d -> m ((= x y).s) e c d")
(defrecord i-eq [] Instruction
  (instr-name [_] "EQ")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (pop (pop (-> regs :stack)))
                                              (= (first (-> regs :stack))
                                                 (second (-> regs :stack))))))]
      (set-regs state (fun regs)))))
(def EQ (i-eq.))

;; Negates logical value on top of the stack
;; m (x.s) e (NOT.c) d -> m ((not x).s) e c d")
(defrecord i-not [] Instruction
  (instr-name [_] "NOT")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :stack (conj
                                              (pop (-> regs :stack))
                                              (not (first (-> regs :stack))))))]
      (set-regs state (fun regs)))))
(def NOT (i-not.))

;; If top of the stack if true, executes optional instruction list
;; m (T . s) e (SEL f .c) d -> m s e f (c.d)
;; m (nil.s) e (SEL f .c) d -> m s e c d
(defrecord i-sel [] Instruction
  (instr-name [_] "SEL")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (if (first (:stack regs))
                           (assoc regs :stack (pop (:stack regs))
                                       :code (first (:code regs))
                                       :dump (list (pop (:code regs)) (:dump regs)))
                           (assoc regs :stack (pop (:stack regs))
                                       :code (pop (:code regs)))))]
      (set-regs state (fun regs)))))
(def SEL (i-sel.))

;; Return from an optional instruction list
;; m s e (JOIN) (c.d) -> m s e c d
(defrecord i-join [] Instruction
  (instr-name [_] "JOIN")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :code (first (:dump regs))
                                     :dump (second (:dump regs))))]
      (set-regs state (fun regs)))))
(def JOIN (i-join.))

;; Load and execute instruction list as a loop
;; That list should end with RPT
;; m s e (LOOP.f c) d -> m s e f (f.c d)
(defrecord i-loop [] Instruction
  (instr-name [_] "LOOP")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (assoc regs :code (first (:code regs))
                                     :dump (list (first (:code regs)) (rest (:code regs)) (:dump regs))))]
      (set-regs state (fun regs)))))
(def LOOP (i-loop.))

;; Repeat or break from loop, depending on top of the stack value
;; Should only be in the end of a loop instruction list, loaded via LOOP
;; m (T . s) e (RPT) (f.c d) -> m s e f (f.c d)
;; m (nil.s) e (RPT) (f.c d) -> m s e c d
(defrecord i-rpt [] Instruction
  (instr-name [_] "RPT")
  (execute [_ state]
    (let [regs (:regs state)
          fun (fn [regs] (if (first (:stack regs))
                           (assoc regs :stack (pop (:stack regs))
                                       :code (first (:dump regs)))
                           (assoc regs :stack (pop (:stack regs))
                                       :code (second (:dump regs))
                                       :dump (nth (:dump regs) 2))))]
      (set-regs state (fun regs)))))
(def RPT (i-rpt.))


;; (msecd-exec (list LDF (list LDC 2 LDC 2 ADD RTN) AP LDC 2 MUL STOP))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def logger (agent nil))

(defn log
  "Logging function for msecd processes.
  Prints msg to standard output with date, time and process id.
  Should only be called from an agent executing msecs process"
  [& msg]
  (let [proc-id (:id @*agent*)
        date-time (.format (LocalDateTime/now) (DateTimeFormatter/ofPattern "HH:mm:ss.SSSSSSS"))
        agent-fn (fn [state & args] (apply println args))]
    (send-off logger agent-fn date-time "PR" proc-id " | " (apply str msg))))

(def running true)

(def debug-log true)

(def pause-time-ms 100)

(def procs (ref {}))

(def next-id (ref 0))

(defn create-process
  "Returns new process as agent with state of id, regs and procs.
  Adds this process to procs.
  - id is new process id
  - regs is starting process registers
  - procs is a ref to map of all processes"
  [regs]
  (let [id @next-id
        new-proc (agent {:id id :status (atom "run") :wait-for (atom nil) :msgs (ref {}) :regs regs})]
    (dosync
      (alter next-id inc)
      (alter procs assoc id new-proc))
    new-proc)
  )

;; should be declared before msecd-exec-agent? this is a workaround
(def WAIT nil)
(def SEND nil)
(def STOP nil)

(defn msecd-exec-agent
  "Function to be sent to agent. Executes one instruction from code register, resends itself to same agent."
  [state]
  (let [regs (:regs state)]

    ;; small pause, should be configurable later
    (Thread/sleep pause-time-ms)

    ;; Send this function to current agent again if all of this is true:
    ;; - machine is running
    ;; - code register is not empty
    ;; - next instruction is not STOP, SEND or WAIT
    ;;
    ;; If next instruction is WAIT or SEND, then this function should be sent to agent in execute call
    ;; for WAIT or SEND in this or another agent.

    (when (and running (and
                         (not (= 0 (count (-> regs :code))))
                         (not (= STOP (first (-> regs :code))))
                         (not (= SEND (first (-> regs :code))))
                         (not (= WAIT (first (-> regs :code))))))
      (send *agent* msecd-exec-agent))

    (log "Going to execute: " (instr-name (first (:code regs))))

    ;; Execute top instruction on code register
    ;; Set registers in state to registers after execution

    (execute
      (first (-> regs :code))
      (set-regs state (assoc regs :code (pop (-> regs :code)))))
    )
  )

(defn wake-up-agent
  "Used to get out of WAIT"
  [state]
  (let [regs (:regs state)
        wait-for @(:wait-for state)
        msg (get @(:msgs state) wait-for)]

    (log "Received wake up call! Was waiting for: " wait-for " Msg: " msg)
    (send *agent* msecd-exec-agent)

    ;(if (not (nil? msg))

      ;; if there is a message
      (dosync
        (alter (:msgs state) dissoc wait-for)
        (reset! (:status state) "run")
        (reset! (:wait-for state) nil)
        (assoc state :regs (assoc regs
                             :stack (conj (:stack regs) msg))))

      ;; if there is no message i.e. when process stopped
      ;(assoc state :status "run" :wait-for nil))
      ))

;; Create new processes that start immediately
;; m (x.s) e (KIT с1 .. cx.c) d -> АМ0 = m s e c d | АМ1 = @m s e с1 d | АМ2 = @m s e с2 d | ... | AX ...
(defrecord i-kit [] Instruction
  (instr-name [_] "KIT")
  (execute [_ state]
    (let [regs (:regs state)]

      (dotimes [i (first (-> regs :stack))]
        (send (create-process (Registers. (:mem regs) nil nil (nth (:code regs) i) nil)) msecd-exec-agent))

      (set-regs state (assoc regs :code (nth
                                          (iterate pop (:code regs))
                                          (first (-> regs :stack)))
                                  :stack (pop (:stack regs)))))))
(def KIT (i-kit.))

;; Stop process execution
;; Wake up other processes waiting for this process
;; m s e (STOP.c) d -> m s e (STOP.c) d
(defrecord i-stop [] Instruction
  (instr-name [_] "STOP")
  (execute [_ state]

    (doseq [proc (vals @procs)]

      (when (= @(:wait-for @proc) (:id @*agent*))
        (log "Waking up " (:id @proc) " because I am going to stop")
        (send proc wake-up-agent)))

    (log "Final result is: " (or (first (:stack (:regs state))) "(empty!)") ". Stopping...")
    (reset! (:status state) "stop")
    state))
(def STOP (i-stop.))

;; Send a message to another process. Blocks until that process receives message.
;;
(defrecord i-send [] Instruction
  (instr-name [_] "SEND")
  (execute [_ state]

    (dosync (let [regs (:regs state)
                  next-regs (assoc regs :code (pop (:code regs))
                                        :stack (pop (:stack regs)))
                  msg (first (:stack regs))
                  my-id (:id @*agent*)
                  recv-id (first (:code regs))
                  recv (get @procs recv-id)]

              (log "SEND: should be sending \"" msg "\" to " recv-id)

              (alter (:msgs @recv) assoc my-id msg)

              (if (= @(:status @recv) "stop")

                ;; do if receiver has already stopped
                (do
                  (log "SEND: receiver has already stopped")
                  (send *agent* msecd-exec-agent)
                  (set-regs state next-regs))

                (if (and (= @(:status @recv) "wait")
                         (= @(:wait-for @recv) my-id))

                  ;; do if receiver is already waiting
                  (do
                    (log "SEND: receiver is ready, sending message and a wake up call")
                    (send recv wake-up-agent)
                    (send *agent* msecd-exec-agent)
                    (set-regs state next-regs))

                  ;; do if receiver is not waiting yet
                  (do
                    (log "SEND: receiver not ready, blocking...")
                    (reset! (:status state) "wait")
                    (reset! (:wait-for state) recv-id)
                    (assoc state :regs next-regs))))))
    ))
(def SEND (i-send.))

;; Waits for a message from another process and puts it into stack.
;; If that process has stopped, nothing is put into stack.
;;
(defrecord i-wait [] Instruction
  (instr-name [_] "WAIT")
  (execute [_ state]

    (dosync (let [regs (:regs state)
                  next-regs (assoc regs :code (pop (:code regs)))
                  my-id (:id @*agent*)
                  sender-id (first (:code regs))
                  sender (get @procs sender-id)
                  msg (get @(:msgs state) sender-id)]

              (log "WAIT: should be waiting for " sender-id)

              (if (= @(:status @sender) "stop")

                ;; do if sender has already stopped
                (do
                  (log "WAIT: sender has already stopped")
                  (send *agent* msecd-exec-agent)
                  (set-regs state (assoc next-regs
                                    :stack (conj (:stack next-regs) nil))))

                (if (nil? msg)

                  ;; do if sender has not sent us anything yet
                  (do
                    (log "WAIT: not received, blocking...")
                    (reset! (:status state) "wait")
                    (reset! (:wait-for state) sender-id)
                    (assoc state :regs next-regs))

                  ;; do if sender has already sent something and is waiting
                  (do
                    (log "WAIT: already received")
                    (send *agent* msecd-exec-agent)
                    (when (and (= @(:status @sender) "wait")
                               (= @(:wait-for @sender) my-id))
                      (log "WAIT: Sending wake up call...")
                      (send sender wake-up-agent))
                    (alter (:msgs state) dissoc sender-id)
                    (set-regs state (assoc next-regs
                                      :stack (conj (:stack next-regs) msg)))))
                )))))
(def WAIT (i-wait.))

;; Sleep for time in milliseconds on top of the stack
(defrecord i-sleep [] Instruction
  (instr-name [_] "SLEEP")
  (execute [_ state]
    (let [regs (:regs state)]
      (Thread/sleep (first (:stack regs)))
      (set-regs state (assoc regs
                        :stack (pop (:stack regs)))))))
(def SLEEP (i-sleep.))

(defn msecd-exec
  ;; "Executes instruction list starting with empty registers. Returns top of the stack." -rewrite doc
  [code]
  (dosync
    (ref-set procs {})
    (ref-set next-id 0))
  (let [main-proc (create-process (Registers. (ref ()) nil nil code nil))]

    ;; make it wait for main process to "stop" ?
    ;; (while (not (= )) )

    (if running
      (send main-proc msecd-exec-agent)
      (println "running is set to false!")))
  )

;; (def main (msecd-exec (list LDC 1 KIT (list LDC 1000 SLEEP LDC "ready" SEND 0 WAIT 0 STOP) WAIT 1 STOP)))