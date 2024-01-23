----------------------------- MODULE TCPmodel1 -----------------------------
EXTENDS Integers, OldReals
CONSTANT Sender, Receiver, Router, Packet
                                                                                                         
VARIABLES pc, now, mss, sequencenumber, window_size, data, router_queue, 
          packet_ubTimer, packet_sequencenumber, packet_data, 
          received_data, received_sequencenumber,
          rto, rto_countTimer, 
          rtpacket_sequencenumber, rtpacket_data, 
          rtpacket_pc, rtpacket_ubTimer, 
          packet_lbTimer, rtpacket_lbTimer
          
vars == <<pc, now, mss, sequencenumber, window_size, data, router_queue, 
          packet_ubTimer, packet_sequencenumber, packet_data, 
          received_data, received_sequencenumber,
          rto, rto_countTimer, 
          rtpacket_sequencenumber, rtpacket_data, 
          rtpacket_pc, rtpacket_ubTimer, 
          packet_lbTimer, rtpacket_lbTimer>>
\*max-min
Max(a,b) == IF a \geq b THEN a ELSE b 

\*Moving Packet Relation  t = packet1 or attacker1 or retransmission packet1 ...
At(t,loc,common_pc)             == common_pc[t] = loc
GoTo(t,loc,common_pc)           == common_pc' =[common_pc EXCEPT ![t]=loc]
GoFromTo(t,loc1,loc2,common_pc) == At(t,loc1,common_pc) /\ GoTo(t,loc2,common_pc)

\*Timer
SetTimer(t,timer,tau) == timer' = [timer EXCEPT ![t] = tau]
\*lower
TimedOut(h,timer) == timer[h] = 0
\*upper
ResetUBTimer(t,timer) == SetTimer(t,timer,Infinity)
 
Init == 
\*packet
/\pc                = [p \in Packet |-> "Senders"] 
/\packet_sequencenumber          = [p \in Packet |-> 1]    
/\packet_data            = [p \in Packet |-> 1000] 
/\packet_ubTimer           = [p \in Packet |-> 100]
/\packet_lbTimer           = [p \in Packet |-> 100]
\*retransmissionpacket
/\rtpacket_pc             = [p \in Packet |-> "NotExist"] 
/\rtpacket_sequencenumber        = [p \in Packet |-> 0]
/\rtpacket_data           = [p \in Packet |-> 0]
/\rtpacket_ubTimer        = [p \in Packet |-> Infinity]
/\rtpacket_lbTimer        = [p \in Packet |-> 0]
\*real time
/\now               = 0
\*rto
/\rto_countTimer  = [p \in Packet |-> 0] 
/\rto               = [p \in Packet |-> 1000] 
\*Sender
/\window_size            = [s \in Sender |-> 1]
/\data              = [s \in Sender |-> 10000]
/\mss               = [s \in Sender |-> 1000] 
/\sequencenumber    = [s \in Sender |-> 1]    
\*Receiver
/\received_data            = [r \in Receiver |-> 0]
/\received_sequencenumber         = [r \in Receiver |-> {}]
\*Router
/\router_queue           = 1000


ReTransmissionTimeout(s,p) == 
/\ rto_countTimer[p] = rto[p]
/\ GoTo(p,"SendingToRouter", rtpacket_pc)
/\ rtpacket_sequencenumber' = [rtpacket_sequencenumber EXCEPT![p] = sequencenumber[s]]
/\ rtpacket_data'   = [rtpacket_data EXCEPT![p] = mss[s]]
/\ rto'       = [rto EXCEPT![p] = 2*rto[p]]
/\ rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
/\ SetTimer(p, rtpacket_ubTimer, 100) 
/\ SetTimer(p, rtpacket_lbTimer, 100)
/\UNCHANGED<<pc, now, mss, sequencenumber, window_size, data, router_queue, packet_ubTimer,
             packet_sequencenumber, packet_data, received_data, received_sequencenumber, 
             packet_lbTimer>>
                              
Senders(s,p) ==
/\At(p, "Senders", pc)
/\TimedOut(p, packet_lbTimer)
/\IF (window_size[s] > 0) /\ (data[s] > 0) 
      THEN
         \*packet
         /\GoFromTo(p, "Senders", "SendingToRouter", pc)
         /\SetTimer(p, packet_ubTimer, 100)
         /\SetTimer(p, packet_lbTimer, 100)
         /\packet_data'           = [packet_data EXCEPT![p] = mss[s]]
         /\packet_sequencenumber' = [packet_sequencenumber EXCEPT![p] = sequencenumber[s]]
         \*sender
         /\data'        = [data EXCEPT![s] = data[s] - mss[s]]
         /\window_size' = [window_size EXCEPT![s] = window_size[s] -1 ]
      ELSE IF (data[s]=0)
                THEN
                    /\GoTo(p,"End", pc)
                    /\SetTimer(p, packet_lbTimer, 0)
                    /\ResetUBTimer(p, packet_ubTimer)
                    /\UNCHANGED<<packet_data, packet_sequencenumber, data, 
                                 window_size>>
                ELSE
                    /\TRUE
                    /\UNCHANGED<<pc, packet_ubTimer, packet_data, packet_sequencenumber, 
                                 data, window_size>>
/\UNCHANGED<<router_queue, sequencenumber, now, mss, received_data, received_sequencenumber,
             rto, rto_countTimer, rtpacket_sequencenumber, rtpacket_data, rtpacket_pc, 
             rtpacket_ubTimer, rtpacket_lbTimer>>


LossDataState(p) ==
/\packet_data'   = [packet_data EXCEPT![p] = 0]
/\packet_sequencenumber' = [packet_sequencenumber EXCEPT![p] = 0]

LossDataStateRp(p) ==
/\rtpacket_data'   = [rtpacket_data EXCEPT![p] = 0]
/\rtpacket_sequencenumber' = [rtpacket_sequencenumber EXCEPT![p] = 0]


LossDataStateRe(p) == 
/\packet_sequencenumber' = [packet_sequencenumber EXCEPT![p] = 0]

LossDataStateReRp(p) == 
/\rtpacket_sequencenumber' = [rtpacket_sequencenumber EXCEPT![p] = 0]














SendingToRouter(p) ==
/\ \/ /\TimedOut(p, packet_lbTimer)
      /\ \/ /\IF (router_queue - packet_data[p] >= 0)
                THEN 
                    /\GoFromTo(p, "SendingToRouter", "Routers", pc)
                    /\SetTimer(p, packet_ubTimer, 100)
                    /\SetTimer(p, packet_lbTimer, 100)
                    /\router_queue' = router_queue - packet_data[p]
                    /\UNCHANGED<<sequencenumber, now ,data, mss, window_size, packet_data, 
                                 packet_sequencenumber, rto, rto_countTimer, 
                                 rtpacket_sequencenumber, 
                                 rtpacket_data, rtpacket_pc, rtpacket_ubTimer>>
                ELSE
                    /\GoFromTo(p, "SendingToRouter", "LossData", pc)
                    /\LossDataState(p)
                    /\ResetUBTimer(p, packet_ubTimer)
                    /\UNCHANGED<<router_queue, sequencenumber, now, data, mss, window_size,
                                 rto, rto_countTimer, rtpacket_sequencenumber, rtpacket_data, 
                                 rtpacket_pc, rtpacket_ubTimer, packet_lbTimer>>
      /\UNCHANGED<<rtpacket_lbTimer>>
      
   \/ /\TimedOut(p, rtpacket_lbTimer)
      /\ \/ /\IF (router_queue - rtpacket_data[p] >= 0)
                THEN 
                    /\GoFromTo(p, "SendingToRouter", "Routers", rtpacket_pc)
                    /\SetTimer(p, rtpacket_ubTimer, 100)
                    /\SetTimer(p, rtpacket_lbTimer, 100)
                    /\router_queue' = router_queue - rtpacket_data[p]
                    /\UNCHANGED<<sequencenumber, now ,data, mss, window_size, packet_ubTimer, 
                                 packet_data, packet_sequencenumber, rto, rto_countTimer, 
                                 rtpacket_sequencenumber, rtpacket_data, pc>>
                ELSE
                    /\GoFromTo(p, "SendingToRouter", "LossData", rtpacket_pc)
                    /\LossDataStateRp(p)
                    /\ResetUBTimer(p, rtpacket_ubTimer)
                    /\UNCHANGED<<router_queue, sequencenumber, now, data, mss, window_size, 
                                 packet_ubTimer, rto, rto_countTimer, packet_sequencenumber,
                                 packet_data, pc, rtpacket_lbTimer>>
      /\UNCHANGED<<packet_lbTimer>>
/\UNCHANGED<<received_data, received_sequencenumber>>

Routers(p) ==
/\ \/ /\At(p, "Routers", pc) 
      /\TimedOut(p, packet_lbTimer)
      /\GoFromTo(p, "Routers", "SendingToReceiver", pc)
      /\SetTimer(p, packet_ubTimer, 100)
      /\SetTimer(p, packet_lbTimer, 100)
      /\ router_queue' = router_queue + packet_data[p]
      /\UNCHANGED<<now, sequencenumber, window_size, data, mss, packet_data,
                   packet_sequencenumber, received_data, received_sequencenumber,
                   rto, rto_countTimer, rtpacket_sequencenumber, rtpacket_data,
                   rtpacket_pc, rtpacket_ubTimer, rtpacket_lbTimer>>
                   
   \/ /\At(p, "Routers", rtpacket_pc) 
      /\TimedOut(p, rtpacket_lbTimer)
      /\GoFromTo(p, "Routers", "SendingToReceiver", rtpacket_pc)
      /\SetTimer(p, rtpacket_ubTimer, 100)
      /\SetTimer(p, rtpacket_lbTimer, 100)
      /\ router_queue' = router_queue + rtpacket_data[p]
      /\UNCHANGED<<now, sequencenumber, window_size, data, mss, packet_data, 
                   packet_sequencenumber, received_data, received_sequencenumber, rto,
                   rto_countTimer, rtpacket_sequencenumber, rtpacket_data, pc,
                   packet_ubTimer, packet_lbTimer>>  

SendingToReceiver(p) ==               
/\ \/ /\SetTimer(p, packet_ubTimer, 100)
      /\TimedOut(p, packet_lbTimer)
      /\SetTimer(p, packet_lbTimer, 100)
      /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers", pc)
            /\UNCHANGED<<now, sequencenumber, window_size, data, mss, packet_data, 
                         packet_sequencenumber, router_queue, received_data, 
                         received_sequencenumber, rto, rto_countTimer, rtpacket_pc, 
                         rtpacket_sequencenumber, rtpacket_data,rtpacket_ubTimer>>
      /\UNCHANGED<<rtpacket_lbTimer>>
      
   \/ /\SetTimer(p, rtpacket_ubTimer, 100)
      /\TimedOut(p, rtpacket_lbTimer)
      /\SetTimer(p, rtpacket_lbTimer, 100)
      /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers", rtpacket_pc)
            /\UNCHANGED<<now, sequencenumber, window_size, data, mss, packet_ubTimer, 
                         packet_data, packet_sequencenumber, router_queue, received_data,
                         received_sequencenumber, rto, rto_countTimer, 
                         rtpacket_sequencenumber, rtpacket_data, pc>>
      /\UNCHANGED<<packet_lbTimer>>  
             
             
             
             
             
             
             
             
             
                              
Receivers(s,p,r) ==
/\ \/ /\GoFromTo(p, "Receivers", "SendingToRouterRe", pc)
      /\SetTimer(p, packet_ubTimer, 100)
      /\TimedOut(p, packet_lbTimer)
      /\SetTimer(p, packet_lbTimer, 100)
      /\IF(packet_sequencenumber[p] \notin received_sequencenumber[r])
           THEN 
               /\received_data'   = [received_data EXCEPT![r] = received_data[r] + packet_data[p]]
           ELSE
               /\received_data'   = [received_data EXCEPT![r] = received_data[r]]
      /\IF(packet_sequencenumber[p] \notin received_sequencenumber[r])
           THEN 
               /\received_sequencenumber' = [received_sequencenumber EXCEPT![r] = 
                                    received_sequencenumber[r] \union {packet_sequencenumber[p]} ]
           ELSE
               /\received_sequencenumber' = [received_sequencenumber EXCEPT![r] 
                                                                     = received_sequencenumber[r]]
      /\UNCHANGED<<now, data, router_queue, mss, sequencenumber, window_size,
                   packet_data, packet_sequencenumber, rto, rto_countTimer, 
                   rtpacket_sequencenumber, rtpacket_data, rtpacket_pc, 
                   rtpacket_ubTimer, rtpacket_lbTimer>>

   \/ /\GoFromTo(p, "Receivers", "SendingToRouterRe", rtpacket_pc)
      /\SetTimer(p, rtpacket_ubTimer, 100)
      /\TimedOut(p, rtpacket_lbTimer)
      /\SetTimer(p, rtpacket_lbTimer, 100)
      /\IF(rtpacket_sequencenumber[p] \notin received_sequencenumber[r])
           THEN 
                /\ received_data' = [received_data EXCEPT![r] = received_data[r] + rtpacket_data[p]]
           ELSE 
                /\ received_data' = [received_data EXCEPT![r] = received_data[r]]
      /\IF(rtpacket_sequencenumber[p] \notin received_sequencenumber[r])
           THEN 
                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = 
                                      received_sequencenumber[r] \union {rtpacket_sequencenumber[p]} ]
           ELSE 
                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] 
                                                                       = received_sequencenumber[r]]
      /\UNCHANGED<<now, data, router_queue, mss, sequencenumber, window_size, packet_data, 
                   packet_sequencenumber, rto, rto_countTimer, rtpacket_sequencenumber,
                   rtpacket_data, pc, packet_ubTimer, packet_lbTimer>>
                                     


SendingToRouterRe(p) ==
/\ \/ /\TimedOut(p, packet_lbTimer)
      /\ \/ /\IF (router_queue - packet_data[p] >= 0)
                 THEN 
                     /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", pc)
                     /\router_queue' = router_queue - packet_data[p]
                     /\SetTimer(p, packet_ubTimer, 100)
                     /\SetTimer(p, packet_lbTimer, 100)
                     /\UNCHANGED<<sequencenumber, now ,data, mss, window_size, packet_data,
                                  packet_sequencenumber, rto, rto_countTimer, 
                                  rtpacket_sequencenumber, rtpacket_data, rtpacket_pc,
                                  rtpacket_ubTimer, rtpacket_lbTimer>>
                 ELSE
                     /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", pc)
                     /\LossDataStateRe(p)
                     /\ResetUBTimer(p, packet_ubTimer)
                     /\UNCHANGED<<router_queue, sequencenumber, now, data, mss, window_size, 
                                  packet_data, rto, rto_countTimer, rtpacket_sequencenumber,
                                  rtpacket_data, rtpacket_pc, rtpacket_ubTimer, rtpacket_lbTimer,
                                  packet_lbTimer>>    
      /\UNCHANGED<<received_data, received_sequencenumber>>

   \/ /\TimedOut(p, rtpacket_lbTimer)
      /\ \/ /\IF (router_queue - rtpacket_data[p] >= 0)
                 THEN 
                     /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", rtpacket_pc)
                     /\SetTimer(p, rtpacket_ubTimer, 100)
                     /\SetTimer(p, rtpacket_lbTimer, 100)
                     /\router_queue' = router_queue - rtpacket_data[p]
                     /\UNCHANGED<<sequencenumber, now ,data, mss, window_size, packet_ubTimer, 
                                  packet_data, packet_sequencenumber, rto, rto_countTimer,
                                  rtpacket_sequencenumber, rtpacket_data, pc, packet_lbTimer>>
                 ELSE
                     /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", rtpacket_pc)
                     /\LossDataStateReRp(p)
                     /\ResetUBTimer(p, rtpacket_ubTimer)
                     /\UNCHANGED<<router_queue, sequencenumber, now, data, mss, window_size,
                                  packet_ubTimer, packet_data, packet_sequencenumber, rto,
                                  rto_countTimer,  pc, packet_sequencenumber, rtpacket_data,
                                  packet_lbTimer, rtpacket_lbTimer>>     
/\UNCHANGED<<received_data, received_sequencenumber>>      
      
RoutersRe(p) ==
/\ \/ /\At(p, "RoutersRe", pc) 
      /\TimedOut(p, packet_lbTimer)
      /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", pc)
      /\router_queue' = router_queue + packet_data[p]
      /\SetTimer(p, packet_ubTimer, 100)
      /\SetTimer(p, packet_lbTimer, 100)
      /\UNCHANGED<<now, sequencenumber, window_size, data, mss, packet_data,
                   packet_sequencenumber, received_data, received_sequencenumber,
                   rto, rto_countTimer, rtpacket_pc,
                   rtpacket_sequencenumber, rtpacket_data, rtpacket_ubTimer, rtpacket_lbTimer>>

   \/ /\At(p, "RoutersRe", rtpacket_pc)
      /\TimedOut(p, rtpacket_lbTimer) 
      /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", rtpacket_pc)
      /\router_queue' = router_queue + rtpacket_data[p]
      /\SetTimer(p, rtpacket_ubTimer, 100)
      /\SetTimer(p, rtpacket_lbTimer, 100)
      /\UNCHANGED<<now, sequencenumber, window_size, data, mss, packet_data,
                   packet_sequencenumber, received_data, received_sequencenumber,
                   rto, rto_countTimer, rtpacket_data,
                   rtpacket_sequencenumber, pc, packet_ubTimer, packet_lbTimer>>

SendingToSenderRe(s,p) ==
/\ \/ /\SetTimer(p, packet_ubTimer, 100)
      /\TimedOut(p, packet_lbTimer)
      /\SetTimer(p, packet_lbTimer, 100)
      /\ \/ /\GoFromTo(p, "SendingToSenderRe", "Senders", pc)
            /\sequencenumber' = [sequencenumber EXCEPT![s] = sequencenumber[s] + mss[s]]
            /\window_size'         = [window_size EXCEPT![s] = window_size[s]+1]
            /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
            /\UNCHANGED<<packet_sequencenumber, rtpacket_sequencenumber, rtpacket_data, 
                         rtpacket_pc, rtpacket_ubTimer>>
      /\UNCHANGED<<now, data, mss, packet_data, received_data, received_sequencenumber,
                   router_queue, rtpacket_lbTimer, rto>>

   \/ /\SetTimer(p, rtpacket_ubTimer, 100)
      /\TimedOut(p, rtpacket_lbTimer)
      /\SetTimer(p, rtpacket_lbTimer, 100)
      /\ \/ /\GoFromTo(p, "SendingToSenderRe", "NotExist", rtpacket_pc)
            /\GoTo(p,"Senders", pc)
            /\sequencenumber'   = [sequencenumber EXCEPT![s] = sequencenumber[s] + mss[s]]
            /\window_size'           = [window_size EXCEPT![s] = window_size[s] + 1]
            /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
            /\UNCHANGED<<packet_sequencenumber, rto, rtpacket_sequencenumber, rtpacket_data, 
                         packet_ubTimer>>
      /\UNCHANGED<<now, data, mss, packet_data, received_data, received_sequencenumber,
                   router_queue, packet_lbTimer, rto>>

\*count time [ms]
PosReal == {100}
Tick == 
\E d \in PosReal:
      /\ \A p \in Packet: packet_ubTimer[p] >= d
      /\ \A rp \in Packet: rtpacket_ubTimer[rp] >= d
      
      /\ \A p \in Packet: rto[p] > rto_countTimer[p] 
 
      /\ now' = now + d
 
      /\ packet_ubTimer' = [p \in Packet |->
                        IF packet_ubTimer[p] = Infinity THEN Infinity
                                                        ELSE packet_ubTimer[p] - d]
      /\ rtpacket_ubTimer' = [rp \in Packet |->
                           IF rtpacket_ubTimer[rp] = Infinity THEN Infinity
                                                              ELSE rtpacket_ubTimer[rp] - d]
                                                       
      /\packet_lbTimer'      = [p \in Packet |-> Max(0, packet_lbTimer[p] - d)]
      /\rtpacket_lbTimer'    = [rp \in Packet |-> Max(0, rtpacket_lbTimer[rp] - d)]
      
      /\rto_countTimer' = [p \in Packet |-> IF (pc[p]#"Senders" /\ pc[p]#"End") 
                                               THEN rto_countTimer[p] + d
                                               ELSE rto_countTimer[p]]
                            
      /\UNCHANGED <<pc, sequencenumber, data, window_size, mss, router_queue, packet_data, 
                    packet_sequencenumber, received_data, received_sequencenumber, rto, 
                    rtpacket_sequencenumber, rtpacket_data, rtpacket_pc>>


Terminating == /\ \A p \in Packet: pc[p] ="End"
               /\ \A p \in Packet: rtpacket_pc[p] ="NotExist"
               /\UNCHANGED vars 

SPNext(s,p,r) == \/Senders(s,p)\/SendingToRouter(p)\/Routers(p)\/SendingToReceiver(p)
                 \/Receivers(s,p,r)\/SendingToRouterRe(p)
                 \/RoutersRe(p)\/SendingToSenderRe(s,p)
                 \/ReTransmissionTimeout(s,p)\*\/Terminating
                   
Next ==  Tick \/ (\E s \in Sender: 
                      \E p \in Packet: 
                           \E r \in Receiver: 
                                             SPNext(s, p, r) )

Liveness ==
    /\ \A s \in Sender: 
             \A p \in Packet: 
                  \A r \in Receiver:
                                    WF_vars( SPNext(s, p, r) )
    /\SF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Liveness

Inv64000 == 
    /\ \A p \in Packet: rto[p] # 64000

InvEnd ==
    /\ \A p \in Packet: pc[p] # "End"

Inv3 ==
    /\  \A p \in Packet: pc[p] # "LossData"  

Inv2000 ==
    /\ \A p \in Packet: rto[p] # 2000


=============================================================================
\* Modification History
\* Last modified Mon Jan 15 13:57:27 JST 2024 by yamatani
\* Created Mon Jan 15 13:00:33 JST 2024 by yamatani
