--------------------------- MODULE TCPmodel2Ver2 ---------------------------
EXTENDS Integers, FiniteSets, OldReals
CONSTANT Sender, Receiver, Router, Packet
                                                                                                           
VARIABLES router_queue, 
          \*Sender  established after  Relation -------------------------------------------------
          mss, sequencenumber, window_size, data,         
          \*Packet Relation ---------------------------------------------------------------------
          pc, packet_sequencenumber, packet_data, 
          \*ReTransmission Packet1 Relation
          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
          \*ReTransmission Packet2 Relation
          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
          \*ReTransmission Packet3 Relation
          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
          \*ReTransmission Packet4 Relation
          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
          \*ReTransmission Packet5 Relation
          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
          \*ReTransmission Pakcet6 Relation
          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
          \*real time ---------------------------------------------------------------------------
          now,
          \*Timer of Packet Relation ------------------------------------------------------------
          packet_ubTimer, packet_lbTimer,
          \*Timer of ReTransmission Packet 1 Relation
          rtpacket_ubTimer1, rtpacket_lbTimer1,
          \*Timer of ReTransmission Packet 2 Relation
          rtpacket_ubTimer2, rtpacket_lbTimer2,
          \*Timer of ReTransmission Packet 3 Relation
          rtpacket_ubTimer3, rtpacket_lbTimer3,
          \*Timer of ReTransmission Packet 4 Relation
          rtpacket_ubTimer4, rtpacket_lbTimer4,
          \*Timer of ReTransmission Packet 5 Relation
          rtpacket_ubTimer5, rtpacket_lbTimer5,
          \*Timer of ReTransmission Packet 6 Relation
          rtpacket_ubTimer6, rtpacket_lbTimer6,       
          \*ReTransmission Time Out Relation
          rto, rto_countTimer,         
          \*Receiver
          received_data, received_sequencenumber

vars == <<router_queue, 
          \*Sender  established after  Relation -------------------------------------------------
          mss, sequencenumber, window_size, data,         
          \*Packet Relation ---------------------------------------------------------------------
          pc, packet_sequencenumber, packet_data, 
          \*ReTransmission Packet1 Relation
          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
          \*ReTransmission Packet2 Relation
          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
          \*ReTransmission Packet3 Relation
          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
          \*ReTransmission Packet4 Relation
          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
          \*ReTransmission Packet5 Relation
          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
          \*ReTransmission Pakcet6 Relation
          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
          \*real time ---------------------------------------------------------------------------
          now,
          \*Timer of Packet Relation ------------------------------------------------------------
          packet_ubTimer, packet_lbTimer,
          \*Timer of ReTransmission Packet 1 Relation
          rtpacket_ubTimer1, rtpacket_lbTimer1,
          \*Timer of ReTransmission Packet 2 Relation
          rtpacket_ubTimer2, rtpacket_lbTimer2,
          \*Timer of ReTransmission Packet 3 Relation
          rtpacket_ubTimer3, rtpacket_lbTimer3,
          \*Timer of ReTransmission Packet 4 Relation
          rtpacket_ubTimer4, rtpacket_lbTimer4,
          \*Timer of ReTransmission Packet 5 Relation
          rtpacket_ubTimer5, rtpacket_lbTimer5,
          \*Timer of ReTransmission Packet 6 Relation
          rtpacket_ubTimer6, rtpacket_lbTimer6,       
          \*ReTransmission Time Out Relation
          rto, rto_countTimer,         
          \*Receiver
          received_data, received_sequencenumber>>

\*max-min
Max(a,b) == IF a \geq b THEN a ELSE b 

\*Moving Packet Relation  t = packet1 or attacker1 or retransmission packet1 ...
At(t,loc,common_pc)             == common_pc[t] = loc
GoTo(t,loc,common_pc)           == common_pc' =[common_pc EXCEPT ![t]=loc]
GoFromTo(t,loc1,loc2,common_pc) == At(t,loc1,common_pc) /\ GoTo(t,loc2,common_pc)

\*Timer Relation
SetTimer(t,timer,tau) == timer' = [timer EXCEPT ![t] = tau]
\*lower bound 
TimedOut(h,timer) == timer[h] = 0
\*upper bound
ResetUBTimer(t,timer) == SetTimer(t,timer,Infinity)

\*Sender Initialize, after established                    Cardinality(Packet)
InitSender == /\window_size           = [s \in Sender |-> Cardinality(Packet)]      \*window size
              /\data                  = [s \in Sender |-> 10000]  \* will send a data
              /\mss                   = [s \in Sender |-> 1000]   \*packet p_data = mss
              /\sequencenumber        = [s \in Sender |-> 1]      \* packet p_seq... = seq...

\*Packet Initialize
InitPacket == /\pc                             = [p \in Packet |-> "Senders"] \* first located
              /\packet_sequencenumber          = [p \in Packet |-> 1]    \* sender seq... = p_seq...
              /\packet_data                    = [p \in Packet |-> 1000] \* sender mss = p _data

\* Helper function to initialize a ReTransmissionPacket
InitReTransmissionPacket ==
    \*ReTransmissionPacket1 Relation
    /\ rtpacket_pc1 = [rp \in Packet |->"NotExist"]
    /\ rtpacket_sequencenumber1 = [rp \in Packet |-> 0]
    /\ rtpacket_data1 = [rp \in Packet |-> 0 ]
    \*ReTransmissionPacket2 Relation
    /\ rtpacket_pc2 = [rp \in Packet |->"NotExist"]
    /\ rtpacket_sequencenumber2 = [rp \in Packet |-> 0]
    /\ rtpacket_data2 = [rp \in Packet |-> 0 ]
    \*ReTransmissionPacket3 Relation
    /\ rtpacket_pc3 = [rp \in Packet |->"NotExist"]
    /\ rtpacket_sequencenumber3 = [rp \in Packet |-> 0]
    /\ rtpacket_data3 = [rp \in Packet |-> 0 ]
    \*ReTransmissionPacket4 Relation
    /\ rtpacket_pc4 = [rp \in Packet |->"NotExist"]
    /\ rtpacket_sequencenumber4 = [rp \in Packet |-> 0]
    /\ rtpacket_data4 = [rp \in Packet |-> 0 ]
    \*ReTransmissionPacket5 Relation
    /\ rtpacket_pc5 = [rp \in Packet |->"NotExist"]
    /\ rtpacket_sequencenumber5 = [rp \in Packet |-> 0]
    /\ rtpacket_data5 = [rp \in Packet |-> 0 ]
    \*ReTransmissionPacket6 Relation
    /\ rtpacket_pc6 = [rp \in Packet |->"NotExist"]
    /\ rtpacket_sequencenumber6 = [rp \in Packet |-> 0]
    /\ rtpacket_data6 = [rp \in Packet |-> 0 ]


\*Timer of Packet, p = packet
InitPacket_Timer == /\packet_ubTimer = [p \in Packet |-> 100]
                    /\packet_lbTimer = [p \in Packet |-> 100]


\*ReTransmission Packet 1       
InitReTransmissionPacket1_Timer == /\rtpacket_ubTimer1 = [rp \in Packet |-> Infinity]
                                   /\rtpacket_lbTimer1 = [rp \in Packet |-> 0]

\*ReTransmission Packet 2       
InitReTransmissionPacket2_Timer == /\rtpacket_ubTimer2 = [rp \in Packet |-> Infinity]
                                   /\rtpacket_lbTimer2 = [rp \in Packet |-> 0]
                               
\*ReTransmission Packet 3
InitReTransmissionPacket3_Timer == /\rtpacket_ubTimer3 = [rp \in Packet |-> Infinity]
                                   /\rtpacket_lbTimer3 = [rp \in Packet |-> 0]
                               
\*ReTransmission Packet 4
InitReTransmissionPacket4_Timer == /\rtpacket_ubTimer4 = [rp \in Packet |-> Infinity]
                                   /\rtpacket_lbTimer4 = [rp \in Packet |-> 0]
                               
\*ReTransmission Packet 5
InitReTransmissionPacket5_Timer == /\rtpacket_ubTimer5 = [rp \in Packet |-> Infinity]
                                   /\rtpacket_lbTimer5 = [rp \in Packet |-> 0]
                               
\*ReTransmission Packet 6
InitReTransmissionPacket6_Timer == /\rtpacket_ubTimer6 = [rp \in Packet |-> Infinity]
                                   /\rtpacket_lbTimer6 =[rp \in Packet |-> 0]
          
\*Timer of ReTransmission Packet, rp = retransmissionpacket
InitReTransmissionPacket_Timer == /\InitReTransmissionPacket1_Timer
                                  /\InitReTransmissionPacket2_Timer
                                  /\InitReTransmissionPacket3_Timer
                                  /\InitReTransmissionPacket4_Timer
                                  /\InitReTransmissionPacket5_Timer
                                  /\InitReTransmissionPacket6_Timer
                              
\*Useing ReTransmissionPacket Timer
\*InitReTransmissionPacket_Timer == /\


Init == \*Sender = portnumber? established before determination
        /\InitSender
        \*packet
        /\InitPacket
        \*retransmisson packet 
        /\InitReTransmissionPacket
        \*time
        /\now = 0
        \* packet sending timer
        /\InitPacket_Timer
        \* ReTransmisson Packet Sending Timer
        /\InitReTransmissionPacket_Timer
        \*ReTransmission Timedout 
        /\rto = [p \in Packet |-> 1000]  \*second [s] 1[s] = 1000[ms]
        /\rto_countTimer  = [p \in Packet |-> 0] \*1000[ms] = 1[s]
        \*Receiver
        /\received_data                     = [r \in Receiver |-> 0]
        /\received_sequencenumber          = [r \in Receiver |-> {}]
        \*Router
        /\router_queue            = 1000*Cardinality(Packet)


\*RTO
ReTransmissionTimeout1(s, p, retransmissionpacket_pc,retransmissionpacket_sequencenumber, retransmissionpacket_data,retransmissionpacket_ubTimer,
                       retransmissionpacket_lbTimer) == 
                                 /\ rto_countTimer[p] = rto[p]
                                 /\ GoTo(p,"SendingToRouter",retransmissionpacket_pc)
                                 /\ retransmissionpacket_sequencenumber' = [retransmissionpacket_sequencenumber EXCEPT![p] = packet_sequencenumber[p]]
                                 /\ retransmissionpacket_data'   = [retransmissionpacket_data EXCEPT![p] = packet_data[p]]
                                 /\ rto'       = [rto EXCEPT![p] = 2*rto[p]]
                                 /\ rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                 /\ SetTimer(p, retransmissionpacket_ubTimer, 100) 
                                 /\ SetTimer(p, retransmissionpacket_lbTimer, 100)
                                 /\UNCHANGED <<router_queue,
                                             mss, sequencenumber, window_size, data,         
                                             pc, packet_sequencenumber, packet_data,  
                                             rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                             rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                             rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                             rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                             rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                             now,
                                             packet_ubTimer, packet_lbTimer,
                                             rtpacket_ubTimer2, rtpacket_lbTimer2,
                                             rtpacket_ubTimer3, rtpacket_lbTimer3,
                                             rtpacket_ubTimer4, rtpacket_lbTimer4,
                                             rtpacket_ubTimer5, rtpacket_lbTimer5,
                                             rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                             received_data, received_sequencenumber>>

ReTransmissionTimeout2(s, p, retransmissionpacket_pc,retransmissionpacket_sequencenumber, retransmissionpacket_data,retransmissionpacket_ubTimer,
                       retransmissionpacket_lbTimer) == 
                                 /\ rto_countTimer[p] = rto[p]
                                 /\ GoTo(p,"SendingToRouter",retransmissionpacket_pc)
                                 /\ retransmissionpacket_sequencenumber' = [retransmissionpacket_sequencenumber EXCEPT![p] = packet_sequencenumber[p]]
                                 /\ retransmissionpacket_data'   = [retransmissionpacket_data EXCEPT![p] = mss[s]]
                                 /\ rto'       = [rto EXCEPT![p] = 2*rto[p]]
                                 /\ rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                 /\ SetTimer(p, retransmissionpacket_ubTimer, 100) 
                                 /\ SetTimer(p, retransmissionpacket_lbTimer, 100)
                                 /\UNCHANGED <<router_queue,
                                             mss, sequencenumber, window_size, data,         
                                             pc, packet_sequencenumber, packet_data, 
                                             rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                             rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                             rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                             rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                             rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                             now,
                                             packet_ubTimer, packet_lbTimer,
                                             rtpacket_ubTimer1, rtpacket_lbTimer1,
                                             rtpacket_ubTimer3, rtpacket_lbTimer3,
                                             rtpacket_ubTimer4, rtpacket_lbTimer4,
                                             rtpacket_ubTimer5, rtpacket_lbTimer5,
                                             rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                             received_data, received_sequencenumber>>

ReTransmissionTimeout3(s, p, retransmissionpacket_pc,retransmissionpacket_sequencenumber, retransmissionpacket_data,retransmissionpacket_ubTimer,
                       retransmissionpacket_lbTimer) == 
                                 /\ rto_countTimer[p] = rto[p]
                                 /\ GoTo(p,"SendingToRouter",retransmissionpacket_pc)
                                 /\ retransmissionpacket_sequencenumber' = [retransmissionpacket_sequencenumber EXCEPT![p] = packet_sequencenumber[p]]
                                 /\ retransmissionpacket_data'   = [retransmissionpacket_data EXCEPT![p] = mss[s]]
                                 /\ rto'       = [rto EXCEPT![p] = 2*rto[p]]
                                 /\ rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                 /\ SetTimer(p, retransmissionpacket_ubTimer, 100) 
                                 /\ SetTimer(p, retransmissionpacket_lbTimer, 100)
                                 /\UNCHANGED <<router_queue, 
                                             mss, sequencenumber, window_size, data,         
                                             pc, packet_sequencenumber, packet_data, 
                                             rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                             rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                             rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                             rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                             rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                             now,
                                             packet_ubTimer, packet_lbTimer,
                                             rtpacket_ubTimer1, rtpacket_lbTimer1,
                                             rtpacket_ubTimer2, rtpacket_lbTimer2,
                                             rtpacket_ubTimer4, rtpacket_lbTimer4,
                                             rtpacket_ubTimer5, rtpacket_lbTimer5,
                                             rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                             received_data, received_sequencenumber>>

ReTransmissionTimeout4(s, p, retransmissionpacket_pc,retransmissionpacket_sequencenumber, retransmissionpacket_data,retransmissionpacket_ubTimer,
                       retransmissionpacket_lbTimer) == 
                                 /\ rto_countTimer[p] = rto[p]
                                 /\ GoTo(p,"SendingToRouter",retransmissionpacket_pc)
                                 /\ retransmissionpacket_sequencenumber' = [retransmissionpacket_sequencenumber EXCEPT![p] = packet_sequencenumber[p]]
                                 /\ retransmissionpacket_data'   = [retransmissionpacket_data EXCEPT![p] = mss[s]]
                                 /\ rto'       = [rto EXCEPT![p] = 2*rto[p]]
                                 /\ rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                 /\ SetTimer(p, retransmissionpacket_ubTimer, 100) 
                                 /\ SetTimer(p, retransmissionpacket_lbTimer, 100)
                                 /\UNCHANGED <<router_queue,
                                             mss, sequencenumber, window_size, data,         
                                             pc, packet_sequencenumber, packet_data, 
                                             rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                             rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                             rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                             rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                             rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                             now,
                                             packet_ubTimer, packet_lbTimer,
                                             rtpacket_ubTimer1, rtpacket_lbTimer1,
                                             rtpacket_ubTimer2, rtpacket_lbTimer2,
                                             rtpacket_ubTimer3, rtpacket_lbTimer3,
                                             rtpacket_ubTimer5, rtpacket_lbTimer5,
                                             rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                             received_data, received_sequencenumber>>

ReTransmissionTimeout5(s, p, retransmissionpacket_pc,retransmissionpacket_sequencenumber, retransmissionpacket_data,retransmissionpacket_ubTimer,
                       retransmissionpacket_lbTimer) == 
                                 /\ rto_countTimer[p] = rto[p]
                                 /\ GoTo(p,"SendingToRouter",retransmissionpacket_pc)
                                 /\ retransmissionpacket_sequencenumber' = [retransmissionpacket_sequencenumber EXCEPT![p] = packet_sequencenumber[p]]
                                 /\ retransmissionpacket_data'   = [retransmissionpacket_data EXCEPT![p] = mss[s]]
                                 /\ rto'       = [rto EXCEPT![p] = 2*rto[p]]
                                 /\ rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                 /\ SetTimer(p, retransmissionpacket_ubTimer, 100) 
                                 /\ SetTimer(p, retransmissionpacket_lbTimer, 100)
                                 /\UNCHANGED <<router_queue,
                                             mss, sequencenumber, window_size, data,         
                                             pc, packet_sequencenumber, packet_data, 
                                             rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                             rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                             rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                             rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                             rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                             now,
                                             packet_ubTimer, packet_lbTimer,
                                             rtpacket_ubTimer1, rtpacket_lbTimer1,
                                             rtpacket_ubTimer2, rtpacket_lbTimer2,
                                             rtpacket_ubTimer3, rtpacket_lbTimer3,
                                             rtpacket_ubTimer4, rtpacket_lbTimer4,
                                             rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                             received_data, received_sequencenumber>>

ReTransmissionTimeout6(s, p, retransmissionpacket_pc,retransmissionpacket_sequencenumber, retransmissionpacket_data,retransmissionpacket_ubTimer,
                       retransmissionpacket_lbTimer) == 
                                 /\ rto_countTimer[p] = rto[p]
                                 /\ GoTo(p,"SendingToRouter",retransmissionpacket_pc)
                                 /\ retransmissionpacket_sequencenumber' = [retransmissionpacket_sequencenumber EXCEPT![p] = packet_sequencenumber[p]]
                                 /\ retransmissionpacket_data'   = [retransmissionpacket_data EXCEPT![p] = mss[s]]
                                 /\ rto'       = [rto EXCEPT![p] = 2*rto[p]]
                                 /\ rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                 /\ SetTimer(p, retransmissionpacket_ubTimer, 100) 
                                 /\ SetTimer(p, retransmissionpacket_lbTimer, 100)
                                 /\UNCHANGED <<router_queue,
                                             mss, sequencenumber, window_size, data,         
                                             pc, packet_sequencenumber, packet_data, 
                                             rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                             rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                             rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                             rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                             rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                             now,
                                             packet_ubTimer, packet_lbTimer,
                                             rtpacket_ubTimer1, rtpacket_lbTimer1,
                                             rtpacket_ubTimer2, rtpacket_lbTimer2,
                                             rtpacket_ubTimer3, rtpacket_lbTimer3,
                                             rtpacket_ubTimer4, rtpacket_lbTimer4,
                                             rtpacket_ubTimer5, rtpacket_lbTimer5,      
                                             received_data, received_sequencenumber>>

ReTransmissionTimeout(s, p)    == /\ \/ /\rto[p] = 1000
                                        /\pc[p] # "End"
                                        /\ReTransmissionTimeout1(s, p, rtpacket_pc1,rtpacket_sequencenumber1, 
                                                             rtpacket_data1,rtpacket_ubTimer1, rtpacket_lbTimer1)

                                     \/ /\rto[p] = 2000
                                        /\pc[p] # "End"           
                                        /\ReTransmissionTimeout2(s, p, rtpacket_pc2,rtpacket_sequencenumber2, 
                                                       rtpacket_data2, rtpacket_ubTimer2, rtpacket_lbTimer2)
                                        
                                                 
                                     \/ /\rto[p] = 4000
                                        /\pc[p] # "End"
                                        /\ReTransmissionTimeout3(s, p, rtpacket_pc3,rtpacket_sequencenumber3, 
                                                       rtpacket_data3,rtpacket_ubTimer3, rtpacket_lbTimer3)
                                        
                                                       
                                     \/ /\rto[p] = 8000
                                        /\pc[p] # "End"
                                        /\ReTransmissionTimeout4(s, p, rtpacket_pc4,rtpacket_sequencenumber4, 
                                                       rtpacket_data4,rtpacket_ubTimer4, rtpacket_lbTimer4)
                                        
                                                       
                                     \/ /\rto[p] = 16000
                                        /\pc[p] # "End"
                                        /\ReTransmissionTimeout5(s, p, rtpacket_pc5,rtpacket_sequencenumber5, 
                                                       rtpacket_data5,rtpacket_ubTimer5, rtpacket_lbTimer5)
                                        
                                                       
                                     \/ /\rto[p] = 32000
                                        /\pc[p] # "End"
                                        /\ReTransmissionTimeout6(s, p, rtpacket_pc6,rtpacket_sequencenumber6, 
                                                       rtpacket_data6,rtpacket_ubTimer6, rtpacket_lbTimer6)
 
                                                                                       
\*After establishing communication, packet send
Senders(s,p) == /\At(p, "Senders",pc)
                /\TimedOut(p, packet_lbTimer)
                \*window size & data size 
                /\IF (window_size[s] > 0) /\ (data[s] > 0) 
                      THEN
                         \*packet relation
                         \*move
                         /\GoFromTo(p, "Senders", "SendingToRouter",pc)
                         \* set timer
                         /\SetTimer(p, packet_ubTimer, 100)
                         /\SetTimer(p, packet_lbTimer, 100)
                         \* packet has data and seq
                         /\packet_data'        = [packet_data EXCEPT![p] = mss[s]]
                         /\packet_sequencenumber'      = [packet_sequencenumber EXCEPT![p] = sequencenumber[s]]
                         \*sender relation
                         \* data decrease
                         /\data'   = [data EXCEPT![s] = data[s] - mss[s]]
                         \* window decrease
                         /\window_size' = [window_size EXCEPT![s] = window_size[s] -1 ]
                         \* seqeuncenumber increase
                         /\sequencenumber' = [sequencenumber EXCEPT![s] = sequencenumber[s] + mss[s]]
                         /\UNCHANGED<<router_queue, mss,      
                                      rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                      rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                      rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                      rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                      rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                      rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                      now, rtpacket_ubTimer1, rtpacket_lbTimer1, rtpacket_ubTimer2,
                                      rtpacket_lbTimer2, rtpacket_ubTimer3, rtpacket_lbTimer3, rtpacket_ubTimer4,
                                      rtpacket_lbTimer4, rtpacket_ubTimer5, rtpacket_lbTimer5, rtpacket_ubTimer6,
                                      rtpacket_lbTimer6, rto, rto_countTimer, received_data, received_sequencenumber>>
                      ELSE IF (data[s]=0)
                                THEN
                                    /\GoTo(p,"End",pc)
                                    /\SetTimer(p, packet_lbTimer, 0)
                                    /\ResetUBTimer(p, packet_ubTimer)
                                    /\UNCHANGED <<router_queue,
                                                  mss, sequencenumber, window_size, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                                ELSE
                                    /\TRUE
                                    /\UNCHANGED <<router_queue,
                                                  mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                          
                                   
\*data loss state
LossDataState(p) == /\packet_data'   = [packet_data EXCEPT![p] = 0]
                    /\packet_sequencenumber' = [packet_sequencenumber EXCEPT![p] = 0]

\*data loss state ReTransmissonTimedout Packet  # 1, 2, 3, 4, 5, 6
LossDataStateRp(p, retransmissionpacket_data, retransmissionpacket_sequencenumber) == 
                       /\retransmissionpacket_data'   = [retransmissionpacket_data EXCEPT![p] = 0]
                       /\retransmissionpacket_sequencenumber' = [retransmissionpacket_sequencenumber EXCEPT![p] = 0]


\*Sending packet    
SendingPacket(p) == /\TimedOut(p, packet_lbTimer)
                    /\At(p, "SendingToRouter", pc)
                    \*arrived
                    /\ \/ /\IF (router_queue - packet_data[p] >= 0)
                               THEN 
                                   /\GoFromTo(p, "SendingToRouter", "Routers", pc)
                                   /\SetTimer(p, packet_ubTimer, 100)
                                   /\SetTimer(p, packet_lbTimer, 100)
                                   \*router buffer
                                   /\router_queue' = router_queue - packet_data[p]
                                   /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                packet_sequencenumber, packet_data, 
                                                rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                now,
                                                rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                rto, rto_countTimer,
                                                received_data, received_sequencenumber>>
                               ELSE\*router queue overflowing
                                   /\GoFromTo(p, "SendingToRouter", "LossData", pc)
                                   \*packet data loss
                                   \*/\LossDataState(p)
                                   /\ResetUBTimer(p, packet_ubTimer)
                                   /\UNCHANGED<<router_queue,
                                                mss, sequencenumber, window_size, data,
                                                packet_sequencenumber, packet_data, 
                                                rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                now,
                                                packet_lbTimer,
                                                rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                rto, rto_countTimer,
                                                received_data, received_sequencenumber>>
                    \*not arrived delete




\*Sneding retransmission packet all    but now not use
SendingRetransmissonPacket1(p, retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_sequencenumber, 
                           retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*arrived
                                  /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                          THEN 
                                              /\GoFromTo(p, "SendingToRouter", "Routers", retransmissionpacket_pc)
                                              /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                              /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                              \*router buffer
                                              /\router_queue' = router_queue - retransmissionpacket_data[p]
                                              /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                          ELSE\*router queue overflowing
                                              /\GoFromTo(p, "SendingToRouter", "LossData", retransmissionpacket_pc)
                                              \*packet data loss
                                              \*/\LossDataStateRp(rp, retransmissionpacket_data ,retransmissionpacket_sequencenumber)
                                              /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                              \*delete UNCHANGED
                                              /\UNCHANGED<<router_queue,
                                                           mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data,
                                                           rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                              \*not arrived
                                              \*delete
                                              \* delete UNCHANGED
SendingRetransmissonPacket2(p, retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_sequencenumber, 
                           retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*arrived
                                  /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                          THEN 
                                              /\GoFromTo(p, "SendingToRouter", "Routers", retransmissionpacket_pc)
                                              /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                              /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                              \*router buffer
                                              /\router_queue' = router_queue - retransmissionpacket_data[p]
                                              /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                          ELSE\*router queue overflowing
                                              /\GoFromTo(p, "SendingToRouter", "LossData", retransmissionpacket_pc)
                                              \*packet data loss
                                              \*/\LossDataStateRp(rp, retransmissionpacket_data ,retransmissionpacket_sequencenumber)
                                              /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                              \*delete UNCHANGED
                                              /\UNCHANGED<<router_queue,
                                                           mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1,
                                                           rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                              \*not arrived
                                              \*delete
                                              \* delete UNCHANGED

SendingRetransmissonPacket3(p, retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_sequencenumber, 
                           retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*arrived
                                  /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                          THEN 
                                              /\GoFromTo(p, "SendingToRouter", "Routers", retransmissionpacket_pc)
                                              /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                              /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                              \*router buffer
                                              /\router_queue' = router_queue - retransmissionpacket_data[p]
                                              /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                          ELSE\*router queue overflowing
                                              /\GoFromTo(p, "SendingToRouter", "LossData", retransmissionpacket_pc)
                                              \*packet data loss
                                              \*/\LossDataStateRp(rp, retransmissionpacket_data ,retransmissionpacket_sequencenumber)
                                              /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                              \*delete UNCHANGED
                                              /\UNCHANGED<<router_queue,
                                                           mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2,
                                                           rtpacket_sequencenumber3, rtpacket_data3,  
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                              \*not arrived
                                              \*delete
                                              \* delete UNCHANGED

SendingRetransmissonPacket4(p, retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_sequencenumber, 
                           retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*arrived
                                  /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                          THEN 
                                              /\GoFromTo(p, "SendingToRouter", "Routers", retransmissionpacket_pc)
                                              /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                              /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                              \*router buffer
                                              /\router_queue' = router_queue - retransmissionpacket_data[p]
                                              /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                          ELSE\*router queue overflowing
                                              /\GoFromTo(p, "SendingToRouter", "LossData", retransmissionpacket_pc)
                                              \*packet data loss
                                              \*/\LossDataStateRp(rp, retransmissionpacket_data ,retransmissionpacket_sequencenumber)
                                              /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                              \*delete UNCHANGED
                                              /\UNCHANGED<<router_queue,
                                                           mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3,
                                                           rtpacket_sequencenumber4, rtpacket_data4,   
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                              \*not arrived
                                              \*delete
                                              \* delete UNCHANGED

SendingRetransmissonPacket5(p, retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_sequencenumber, 
                           retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*arrived
                                  /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                          THEN 
                                              /\GoFromTo(p, "SendingToRouter", "Routers", retransmissionpacket_pc)
                                              /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                              /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                              \*router buffer
                                              /\router_queue' = router_queue - retransmissionpacket_data[p]
                                              /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                          ELSE\*router queue overflowing
                                              /\GoFromTo(p, "SendingToRouter", "LossData", retransmissionpacket_pc)
                                              \*packet data loss
                                              \*/\LossDataStateRp(rp, retransmissionpacket_data ,retransmissionpacket_sequencenumber)
                                              /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                              \*delete UNCHANGED
                                              /\UNCHANGED<<router_queue,
                                                           mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4,
                                                           rtpacket_sequencenumber5, rtpacket_data5,  
                                                           rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_lbTimer5,
                                                           rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                              \*not arrived
                                              \*delete
                                              \* delete UNCHANGED

SendingRetransmissonPacket6(p, retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_sequencenumber, 
                           retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*arrived
                                  /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                          THEN 
                                              /\GoFromTo(p, "SendingToRouter", "Routers", retransmissionpacket_pc)
                                              /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                              /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                              \*router buffer
                                              /\router_queue' = router_queue - retransmissionpacket_data[p]
                                              /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                           rtpacket_sequencenumber6, rtpacket_data6,
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,     
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                          ELSE\*router queue overflowing
                                              /\GoFromTo(p, "SendingToRouter", "LossData", retransmissionpacket_pc)
                                              \*packet data loss
                                              \*/\LossDataStateRp(rp, retransmissionpacket_data ,retransmissionpacket_sequencenumber)
                                              /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                              \*delete UNCHANGED
                                              /\UNCHANGED<<router_queue,
                                                           mss, sequencenumber, window_size, data,         
                                                           pc, packet_sequencenumber, packet_data, 
                                                           rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                           rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                           rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                           rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                           rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5,
                                                           rtpacket_sequencenumber6, rtpacket_data6, 
                                                           now,
                                                           packet_ubTimer, packet_lbTimer,
                                                           rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                           rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                           rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                           rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                           rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                           rtpacket_lbTimer6,       
                                                           rto, rto_countTimer,
                                                           received_data, received_sequencenumber>>
                                              \*not arrived
                                              \*delete
                                              \* delete UNCHANGED


\*packet SendingToRouter        \*sending packet    now not use 
SendingToRouter(p) ==  /\ \/ /\ SendingPacket(p)
                             \* sending ReTransmision packet1
                          \/ /\ SendingRetransmissonPacket1(p, rtpacket_pc1, rtpacket_data1, rtpacket_sequencenumber1,
                                                        rtpacket_lbTimer1, rtpacket_ubTimer1)
                             
                          \* sending ReTransmision packet2
                          \/ /\ SendingRetransmissonPacket2(p, rtpacket_pc2, rtpacket_data2, rtpacket_sequencenumber2,
                                                        rtpacket_lbTimer2, rtpacket_ubTimer2)
                          \* sending ReTransmision packet3
                          \/ /\ SendingRetransmissonPacket3(p, rtpacket_pc3, rtpacket_data3, rtpacket_sequencenumber3,
                                                        rtpacket_lbTimer3, rtpacket_ubTimer3)
                          \* sending ReTransmision packet4
                          \/ /\ SendingRetransmissonPacket4(p, rtpacket_pc4, rtpacket_data4, rtpacket_sequencenumber4,
                                                       rtpacket_lbTimer4, rtpacket_ubTimer4)
                          \* sending ReTransmision packet5
                          \/ /\ SendingRetransmissonPacket5(p, rtpacket_pc5, rtpacket_data5, rtpacket_sequencenumber5,
                                                        rtpacket_lbTimer5, rtpacket_ubTimer5)
                          \* sending ReTransmision packet6
                          \/ /\ SendingRetransmissonPacket6(p, rtpacket_pc6, rtpacket_data6, rtpacket_sequencenumber6,
                                                               rtpacket_lbTimer6, rtpacket_ubTimer6)

\*locatedRouters packet
LocatedRouterPacket(p) == /\At(p, "Routers", pc) 
                          /\TimedOut(p, packet_lbTimer)
                          /\GoFromTo(p, "Routers", "SendingToReceiver", pc)
                          /\SetTimer(p, packet_ubTimer, 100)
                          /\SetTimer(p, packet_lbTimer, 100)
                          /\router_queue' = router_queue + packet_data[p]
                          /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                       packet_sequencenumber, packet_data, 
                                       rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                       rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                       rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                       rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                       rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                       rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                       now,
                                       rtpacket_ubTimer1, rtpacket_lbTimer1,
                                       rtpacket_ubTimer2, rtpacket_lbTimer2,
                                       rtpacket_ubTimer3, rtpacket_lbTimer3,
                                       rtpacket_ubTimer4, rtpacket_lbTimer4,
                                       rtpacket_ubTimer5, rtpacket_lbTimer5,
                                       rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                       rto, rto_countTimer,
                                       received_data, received_sequencenumber>>

\*located Routers retransmission packet
LocatedRouterReTransmissionPacket1(p, retransmissionpacket_pc, retransmissionpacket_data, 
                                  retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) ==
                                  \*locate    
                                  /\At(p, "Routers", retransmissionpacket_pc) 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*timer
                                  /\GoFromTo(p, "Routers", "SendingToReceiver", retransmissionpacket_pc)
                                  /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                  /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                  \*router
                                  /\router_queue' = router_queue +  retransmissionpacket_data[p]
                             \*delete UNCHANGED
                                  /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                               pc, packet_sequencenumber, packet_data, 
                                               rtpacket_sequencenumber1, rtpacket_data1, 
                                               rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                               rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                               rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                               rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                               rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                               now,
                                               packet_ubTimer, packet_lbTimer,
                                               rtpacket_ubTimer2, rtpacket_lbTimer2,
                                               rtpacket_ubTimer3, rtpacket_lbTimer3,
                                               rtpacket_ubTimer4, rtpacket_lbTimer4,
                                               rtpacket_ubTimer5, rtpacket_lbTimer5,
                                               rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                               rto, rto_countTimer,
                                               received_data, received_sequencenumber>>
                                               
LocatedRouterReTransmissionPacket2(p, retransmissionpacket_pc, retransmissionpacket_data, 
                                  retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) ==
                                  \*locate    
                                  /\At(p, "Routers", retransmissionpacket_pc) 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*timer
                                  /\GoFromTo(p, "Routers", "SendingToReceiver", retransmissionpacket_pc)
                                  /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                  /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                  \*router
                                  /\router_queue' = router_queue +  retransmissionpacket_data[p]
                             \*delete UNCHANGED
                                  /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                               pc, packet_sequencenumber, packet_data, 
                                               rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                               rtpacket_sequencenumber2, rtpacket_data2, 
                                               rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                               rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                               rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                               rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                               now,
                                               packet_ubTimer, packet_lbTimer,
                                               rtpacket_ubTimer1, rtpacket_lbTimer1,
                                               rtpacket_ubTimer3, rtpacket_lbTimer3,
                                               rtpacket_ubTimer4, rtpacket_lbTimer4,
                                               rtpacket_ubTimer5, rtpacket_lbTimer5,
                                               rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                               rto, rto_countTimer,
                                               received_data, received_sequencenumber>>

LocatedRouterReTransmissionPacket3(p, retransmissionpacket_pc, retransmissionpacket_data, 
                                  retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) ==
                                  \*locate    
                                  /\At(p, "Routers", retransmissionpacket_pc) 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*timer
                                  /\GoFromTo(p, "Routers", "SendingToReceiver", retransmissionpacket_pc)
                                  /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                  /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                  \*router
                                  /\router_queue' = router_queue +  retransmissionpacket_data[p]
                             \*delete UNCHANGED
                                  /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                               pc, packet_sequencenumber, packet_data, 
                                               rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                               rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                               rtpacket_sequencenumber3, rtpacket_data3, 
                                               rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                               rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                               rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                               now,
                                               packet_ubTimer, packet_lbTimer,
                                               rtpacket_ubTimer1, rtpacket_lbTimer1,
                                               rtpacket_ubTimer2, rtpacket_lbTimer2,
                                               rtpacket_ubTimer4, rtpacket_lbTimer4,
                                               rtpacket_ubTimer5, rtpacket_lbTimer5,
                                               rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                               rto, rto_countTimer,
                                               received_data, received_sequencenumber>>

LocatedRouterReTransmissionPacket4(p, retransmissionpacket_pc, retransmissionpacket_data, 
                                  retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) ==
                                  \*locate    
                                  /\At(p, "Routers", retransmissionpacket_pc) 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*timer
                                  /\GoFromTo(p, "Routers", "SendingToReceiver", retransmissionpacket_pc)
                                  /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                  /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                  \*router
                                  /\router_queue' = router_queue +  retransmissionpacket_data[p]
                             \*delete UNCHANGED
                                  /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                               pc, packet_sequencenumber, packet_data, 
                                               rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                               rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                               rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                               rtpacket_sequencenumber4, rtpacket_data4, 
                                               rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                               rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                               now,
                                               packet_ubTimer, packet_lbTimer,
                                               rtpacket_ubTimer1, rtpacket_lbTimer1,
                                               rtpacket_ubTimer2, rtpacket_lbTimer2,
                                               rtpacket_ubTimer3, rtpacket_lbTimer3,
                                               rtpacket_ubTimer5, rtpacket_lbTimer5,
                                               rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                               rto, rto_countTimer,
                                               received_data, received_sequencenumber>>

LocatedRouterReTransmissionPacket5(p, retransmissionpacket_pc, retransmissionpacket_data, 
                                  retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) ==
                                  \*locate    
                                  /\At(p, "Routers", retransmissionpacket_pc) 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*timer
                                  /\GoFromTo(p, "Routers", "SendingToReceiver", retransmissionpacket_pc)
                                  /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                  /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                  \*router
                                  /\router_queue' = router_queue +  retransmissionpacket_data[p]
                             \*delete UNCHANGED
                                  /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                               pc, packet_sequencenumber, packet_data, 
                                               rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                               rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                               rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                               rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                               rtpacket_sequencenumber5, rtpacket_data5, 
                                               rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                               now,
                                               packet_ubTimer, packet_lbTimer,
                                               rtpacket_ubTimer1, rtpacket_lbTimer1,
                                               rtpacket_ubTimer2, rtpacket_lbTimer2,
                                               rtpacket_ubTimer3, rtpacket_lbTimer3,
                                               rtpacket_ubTimer4, rtpacket_lbTimer4,
                                               rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                               rto, rto_countTimer,
                                               received_data, received_sequencenumber>>

LocatedRouterReTransmissionPacket6(p, retransmissionpacket_pc, retransmissionpacket_data, 
                                  retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) ==
                                  \*locate    
                                  /\At(p, "Routers", retransmissionpacket_pc) 
                                  /\TimedOut(p, retransmissionpacket_lbTimer)
                                  \*timer
                                  /\GoFromTo(p, "Routers", "SendingToReceiver", retransmissionpacket_pc)
                                  /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                  /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                  \*router
                                  /\router_queue' = router_queue +  retransmissionpacket_data[p]
                             \*delete UNCHANGED
                                  /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                               pc, packet_sequencenumber, packet_data, 
                                               rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                               rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                               rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                               rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                               rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                               rtpacket_sequencenumber6, rtpacket_data6,
                                               now,
                                               packet_ubTimer, packet_lbTimer,
                                               rtpacket_ubTimer1, rtpacket_lbTimer1,
                                               rtpacket_ubTimer2, rtpacket_lbTimer2,
                                               rtpacket_ubTimer3, rtpacket_lbTimer3,
                                               rtpacket_ubTimer4, rtpacket_lbTimer4,
                                               rtpacket_ubTimer5, rtpacket_lbTimer5,     
                                               rto, rto_countTimer,
                                               received_data, received_sequencenumber>>
                                                                                          
                                               
\*located Router             \*packet
Routers(p)         ==  /\ \/ /\LocatedRouterPacket(p)
                             \*ReTransmisson Packet1
                          \/ /\LocatedRouterReTransmissionPacket1(p, rtpacket_pc1, rtpacket_data1, 
                                                               rtpacket_lbTimer1, rtpacket_ubTimer1)
                             \*ReTransmisson Packet2                                 
                          \/ /\LocatedRouterReTransmissionPacket2(p, rtpacket_pc2, rtpacket_data2, 
                                                               rtpacket_lbTimer2, rtpacket_ubTimer2)
                             \*ReTransmisson Packet3
                          \/ /\LocatedRouterReTransmissionPacket3(p, rtpacket_pc3, rtpacket_data3, 
                                                               rtpacket_lbTimer3, rtpacket_ubTimer3)
                             \*ReTransmisson Packet4
                          \/ /\LocatedRouterReTransmissionPacket4(p, rtpacket_pc4, rtpacket_data4, 
                                                               rtpacket_lbTimer4, rtpacket_ubTimer4)
                             \*ReTransmisson Packet5
                          \/ /\LocatedRouterReTransmissionPacket5(p, rtpacket_pc5, rtpacket_data5, 
                                                               rtpacket_lbTimer5, rtpacket_ubTimer5)
                             \*ReTransmisson Packet6
                          \/ /\LocatedRouterReTransmissionPacket6(p, rtpacket_pc6, rtpacket_data6, 
                                                               rtpacket_lbTimer6, rtpacket_ubTimer6) 

\*packet sendi receiver
SendingPacketReceiver(p) == /\SetTimer(p, packet_ubTimer, 100)
                            /\TimedOut(p, packet_lbTimer)
                            /\SetTimer(p, packet_lbTimer, 100)
                                  \*arrived
                            /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers",pc)
                                  \*delete UNCHANGED
                                  /\UNCHANGED<<router_queue,
                                               mss, sequencenumber, window_size, data,         
                                               packet_sequencenumber, packet_data, 
                                               rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                               rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                               rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                               rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                               rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                               rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                               now,
                                               rtpacket_ubTimer1, rtpacket_lbTimer1,
                                               rtpacket_ubTimer2, rtpacket_lbTimer2,
                                               rtpacket_ubTimer3, rtpacket_lbTimer3,
                                               rtpacket_ubTimer4, rtpacket_lbTimer4,
                                               rtpacket_ubTimer5, rtpacket_lbTimer5,
                                               rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                               rto, rto_countTimer,
                                               received_data, received_sequencenumber>>
                                  \*failure
                                  \*delete

\*retransmission packet send receiver
SengindRetransmissionPacketReceiver1(p, retransmissionpacket_pc, 
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                        /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                        /\TimedOut(p, retransmissionpacket_lbTimer)
                        /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                        \*arrived
                        /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers", retransmissionpacket_pc)
                        /\UNCHANGED<<router_queue,
                                  mss, sequencenumber, window_size, data,         
                                  pc, packet_sequencenumber, packet_data, 
                                  rtpacket_sequencenumber1, rtpacket_data1, 
                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                  now,
                                  packet_ubTimer, packet_lbTimer,
                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                  rto, rto_countTimer,
                                  received_data, received_sequencenumber>>

SengindRetransmissionPacketReceiver2(p, retransmissionpacket_pc, 
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                        /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                        /\TimedOut(p, retransmissionpacket_lbTimer)
                        /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                        \*arrived
                        /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers", retransmissionpacket_pc)
                        /\UNCHANGED<<router_queue,
                                  mss, sequencenumber, window_size, data,         
                                  pc, packet_sequencenumber, packet_data, 
                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                  rtpacket_sequencenumber2, rtpacket_data2, 
                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                  now,
                                  packet_ubTimer, packet_lbTimer,
                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                  rto, rto_countTimer,
                                  received_data, received_sequencenumber>>

SengindRetransmissionPacketReceiver3(p, retransmissionpacket_pc, 
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                        /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                        /\TimedOut(p, retransmissionpacket_lbTimer)
                        /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                        \*arrived
                        /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers", retransmissionpacket_pc)
                        /\UNCHANGED<<router_queue,
                                  mss, sequencenumber, window_size, data,         
                                  pc, packet_sequencenumber, packet_data, 
                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                  rtpacket_sequencenumber3, rtpacket_data3, 
                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                  now,
                                  packet_ubTimer, packet_lbTimer,
                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                  rto, rto_countTimer,
                                  received_data, received_sequencenumber>>

SengindRetransmissionPacketReceiver4(p, retransmissionpacket_pc, 
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                        /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                        /\TimedOut(p, retransmissionpacket_lbTimer)
                        /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                        \*arrived
                        /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers", retransmissionpacket_pc)
                        /\UNCHANGED<<router_queue,
                                  mss, sequencenumber, window_size, data,         
                                  pc, packet_sequencenumber, packet_data, 
                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                  rtpacket_sequencenumber4, rtpacket_data4, 
                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                  now,
                                  packet_ubTimer, packet_lbTimer,
                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                  rto, rto_countTimer,
                                  received_data, received_sequencenumber>>

SengindRetransmissionPacketReceiver5(p, retransmissionpacket_pc, 
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                        /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                        /\TimedOut(p, retransmissionpacket_lbTimer)
                        /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                        \*arrived
                        /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers", retransmissionpacket_pc)
                        /\UNCHANGED<<router_queue,
                                  mss, sequencenumber, window_size, data,         
                                  pc, packet_sequencenumber, packet_data, 
                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                  rtpacket_sequencenumber5, rtpacket_data5, 
                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                  now,
                                  packet_ubTimer, packet_lbTimer,
                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                  rto, rto_countTimer,
                                  received_data, received_sequencenumber>>

SengindRetransmissionPacketReceiver6(p, retransmissionpacket_pc, 
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                        /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                        /\TimedOut(p, retransmissionpacket_lbTimer)
                        /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                        \*arrived
                        /\ \/ /\GoFromTo(p, "SendingToReceiver", "Receivers", retransmissionpacket_pc)
                        /\UNCHANGED<<router_queue,
                                  mss, sequencenumber, window_size, data,         
                                  pc, packet_sequencenumber, packet_data, 
                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                  rtpacket_sequencenumber6, rtpacket_data6,
                                  now,
                                  packet_ubTimer, packet_lbTimer,
                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                  rtpacket_ubTimer5, rtpacket_lbTimer5,    
                                  rto, rto_countTimer,
                                  received_data, received_sequencenumber>>

\*sendingToReceiver              \*packet   
SendingToReceiver(p)    == /\ \/ /\SendingPacketReceiver(p)
                                 \*ReTransmissonPacket1
                              \/ /\SengindRetransmissionPacketReceiver1(p, rtpacket_pc1, 
                                    rtpacket_ubTimer1, rtpacket_lbTimer1)
                                 \*ReTransmissonPacket2
                              \/ /\SengindRetransmissionPacketReceiver2(p, rtpacket_pc2, 
                                    rtpacket_ubTimer2, rtpacket_lbTimer2)
                                 \*ReTransmissonPacket3
                              \/ /\SengindRetransmissionPacketReceiver3(p, rtpacket_pc3, 
                                    rtpacket_ubTimer3, rtpacket_lbTimer3)
                                 \*ReTransmissonPacket4
                              \/ /\SengindRetransmissionPacketReceiver4(p, rtpacket_pc4, 
                                    rtpacket_ubTimer4, rtpacket_lbTimer4)
                                 \*ReTransmissonPacket5
                              \/ /\SengindRetransmissionPacketReceiver5(p, rtpacket_pc5, 
                                    rtpacket_ubTimer5, rtpacket_lbTimer5)
                                 \*ReTransmissonPacket6
                              \/ /\SengindRetransmissionPacketReceiver6(p, rtpacket_pc6, 
                                    rtpacket_ubTimer6, rtpacket_lbTimer6)      

LocatedReceiverPacket(p,r) == /\GoFromTo(p, "Receivers", "SendingToRouterRe",pc)
                              /\SetTimer(p, packet_ubTimer, 100)
                              /\TimedOut(p, packet_lbTimer)
                              /\SetTimer(p, packet_lbTimer, 100)
                              \*receiver data and sequencenumber  add
                              /\IF(packet_sequencenumber[p] \notin received_sequencenumber[r])
                                   THEN 
                                       /\received_data'   = [received_data EXCEPT![r] = received_data[r] + packet_data[p]]
                                   ELSE
                                       /\received_data'   = [received_data EXCEPT![r] = received_data[r]]
                              /\IF(packet_sequencenumber[p] \notin received_sequencenumber[r])
                                   THEN 
                                       /\received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r] \union {packet_sequencenumber[p]} ]
                                   ELSE
                                       /\received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r]]
                              /\UNCHANGED<<router_queue,
                                          mss, sequencenumber, window_size, data,         
                                          packet_sequencenumber, packet_data, 
                                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                          now,
                                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                          rto, rto_countTimer>>
                          

LocatedReceiverReTransmissionPacket1(p, r, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                    /\GoFromTo(p, "Receivers", "SendingToRouterRe",retransmissionpacket_pc)
                                    /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                    /\TimedOut(p, retransmissionpacket_lbTimer)
                                    /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                    \*receiver data and sequencenumber  add
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r] + retransmissionpacket_data[p]]
                                          ELSE 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r]]
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r] \union {retransmissionpacket_sequencenumber[p]} ]
                                          ELSE 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r]]
                                    /\UNCHANGED<<router_queue,
                                          mss, sequencenumber, window_size, data,         
                                          pc, packet_sequencenumber, packet_data, 
                                          rtpacket_sequencenumber1, rtpacket_data1, 
                                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                          now,
                                          packet_ubTimer, packet_lbTimer,
                                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                          rto, rto_countTimer>>

LocatedReceiverReTransmissionPacket2(p, r, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                    /\GoFromTo(p, "Receivers", "SendingToRouterRe",retransmissionpacket_pc)
                                    /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                    /\TimedOut(p, retransmissionpacket_lbTimer)
                                    /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                    \*receiver data and sequencenumber  add
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r] + retransmissionpacket_data[p]]
                                          ELSE 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r]]
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r] \union {retransmissionpacket_sequencenumber[p]} ]
                                          ELSE 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r]]
                                    /\UNCHANGED<<router_queue,
                                          mss, sequencenumber, window_size, data,         
                                          pc, packet_sequencenumber, packet_data, 
                                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                          rtpacket_sequencenumber2, rtpacket_data2, 
                                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                          now,
                                          packet_ubTimer, packet_lbTimer,
                                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                          rto, rto_countTimer>>

LocatedReceiverReTransmissionPacket3(p, r, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                    /\GoFromTo(p, "Receivers", "SendingToRouterRe",retransmissionpacket_pc)
                                    /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                    /\TimedOut(p, retransmissionpacket_lbTimer)
                                    /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                    \*receiver data and sequencenumber  add
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r] + retransmissionpacket_data[p]]
                                          ELSE 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r]]
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r] \union {retransmissionpacket_sequencenumber[p]} ]
                                          ELSE 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r]]
                                    /\UNCHANGED<<router_queue,
                                          mss, sequencenumber, window_size, data,         
                                          pc, packet_sequencenumber, packet_data, 
                                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                          rtpacket_sequencenumber3, rtpacket_data3, 
                                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                          now,
                                          packet_ubTimer, packet_lbTimer,
                                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                          rto, rto_countTimer>>

LocatedReceiverReTransmissionPacket4(p, r, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                    /\GoFromTo(p, "Receivers", "SendingToRouterRe",retransmissionpacket_pc)
                                    /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                    /\TimedOut(p, retransmissionpacket_lbTimer)
                                    /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                    \*receiver data and sequencenumber  add
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r] + retransmissionpacket_data[p]]
                                          ELSE 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r]]
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r] \union {retransmissionpacket_sequencenumber[p]} ]
                                          ELSE 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r]]
                                    /\UNCHANGED<<router_queue,
                                          mss, sequencenumber, window_size, data,         
                                          pc, packet_sequencenumber, packet_data, 
                                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                          rtpacket_sequencenumber4, rtpacket_data4, 
                                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                          now,
                                          packet_ubTimer, packet_lbTimer,
                                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                          rto, rto_countTimer>>

LocatedReceiverReTransmissionPacket5(p, r, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                    /\GoFromTo(p, "Receivers", "SendingToRouterRe",retransmissionpacket_pc)
                                    /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                    /\TimedOut(p, retransmissionpacket_lbTimer)
                                    /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                    \*receiver data and sequencenumber  add
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r] + retransmissionpacket_data[p]]
                                          ELSE 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r]]
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r] \union {retransmissionpacket_sequencenumber[p]} ]
                                          ELSE 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r]]
                                    /\UNCHANGED<<router_queue,
                                          mss, sequencenumber, window_size, data,         
                                          pc, packet_sequencenumber, packet_data, 
                                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                          rtpacket_sequencenumber5, rtpacket_data5, 
                                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                          now,
                                          packet_ubTimer, packet_lbTimer,
                                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                          rto, rto_countTimer>>

LocatedReceiverReTransmissionPacket6(p, r, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                    retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                    /\GoFromTo(p, "Receivers", "SendingToRouterRe",retransmissionpacket_pc)
                                    /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                    /\TimedOut(p, retransmissionpacket_lbTimer)
                                    /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                    \*receiver data and sequencenumber  add
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r] + retransmissionpacket_data[p]]
                                          ELSE 
                                                /\ received_data' = [received_data EXCEPT![r] = received_data[r]]
                                    /\IF(retransmissionpacket_sequencenumber[p] \notin received_sequencenumber[r])
                                          THEN 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r] \union {retransmissionpacket_sequencenumber[p]} ]
                                          ELSE 
                                                /\ received_sequencenumber' = [received_sequencenumber EXCEPT![r] = received_sequencenumber[r]]
                                    /\UNCHANGED<<router_queue,
                                          mss, sequencenumber, window_size, data,         
                                          pc, packet_sequencenumber, packet_data, 
                                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                          rtpacket_sequencenumber6, rtpacket_data6,
                                          now,
                                          packet_ubTimer, packet_lbTimer,
                                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                                          rtpacket_ubTimer5, rtpacket_lbTimer5,  
                                          rto, rto_countTimer>>

\*located receivers   
Receivers(s,p,r) ==  \*arrived Packet
                     /\ \/ /\LocatedReceiverPacket(p, r)
                        \*arrived ReTransmisson Packet1
                        \/ /\LocatedReceiverReTransmissionPacket1(p, r, rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1,
                                                                 rtpacket_ubTimer1, rtpacket_lbTimer1)
                        \*arrived ReTransmisson Packet2
                        \/ /\LocatedReceiverReTransmissionPacket2(p, r, rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2,
                                                                 rtpacket_ubTimer2, rtpacket_lbTimer2)                    
                        \*arrived ReTransmisson Packet3
                        \/ /\LocatedReceiverReTransmissionPacket3(p, r, rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3,
                                                                 rtpacket_ubTimer3, rtpacket_lbTimer3)
                        \*arrived ReTransmisson Packet4
                        \/ /\LocatedReceiverReTransmissionPacket4(p, r, rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4,
                                                                 rtpacket_ubTimer4, rtpacket_lbTimer4)
                        \*arrived ReTransmisson Packet5
                        \/ /\LocatedReceiverReTransmissionPacket5(p, r, rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5,
                                                                 rtpacket_ubTimer5, rtpacket_lbTimer5)
                        \*arrived ReTransmisson Packet6
                        \/ /\LocatedReceiverReTransmissionPacket6(p, r, rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                                 rtpacket_ubTimer6, rtpacket_lbTimer6)


\*loss Data return state
LossDataStateRe(p) == /\ packet_sequencenumber' = [packet_sequencenumber EXCEPT![p] = packet_sequencenumber[p]]
\*loss Data return state ReTransmissionPacket
LossDataStateReRp(p, retransmissionpacket_sequencenumber) == 
                    /\ retransmissionpacket_sequencenumber' = [retransmissionpacket_sequencenumber EXCEPT![p] = retransmissionpacket_sequencenumber[p]]

\*send packet router return
SendingPacketRouterRe(p) == /\TimedOut(p, packet_lbTimer)
                                  \*arrived
                            /\ \/ /\IF (router_queue - packet_data[p] >= 0)
                                       THEN 
                                           /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", pc)
                                           \*router buffer
                                           /\router_queue' = router_queue - packet_data[p]
                                           /\SetTimer(p, packet_ubTimer, 100)
                                           /\SetTimer(p, packet_lbTimer, 100)
                                           /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                                           
                                       ELSE\*router queue overflowing
                                           /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", pc)
                                           \*packet data loss
                                           /\LossDataStateRe(p)
                                           /\ResetUBTimer(p, packet_ubTimer)
                                           /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, window_size, data,         
                                                  packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                               \*not arrived
                               \*delete    

SengindRetransmissionPacketRouterRe1(p, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                                                 retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                            /\TimedOut(p, retransmissionpacket_lbTimer)
                            \*arrived
                            /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                        THEN 
                                            /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", retransmissionpacket_pc)
                                            /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                            /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                            \*router buffer
                                            /\router_queue' = router_queue - retransmissionpacket_data[p]
                                            /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                                        ELSE\*router queue overflowing
                                            /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", retransmissionpacket_pc)
                                            \*packet data loss
                                            /\LossDataStateReRp(p, retransmissionpacket_sequencenumber)
                                            /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                            /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                               \*not arrived
                               \*delete        

SengindRetransmissionPacketRouterRe2(p, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                                                 retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                            /\TimedOut(p, retransmissionpacket_lbTimer)
                            \*arrived
                            /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                        THEN 
                                            /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", retransmissionpacket_pc)
                                            /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                            /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                            \*router buffer
                                            /\router_queue' = router_queue - retransmissionpacket_data[p]
                                            /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                                        ELSE\*router queue overflowing
                                            /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", retransmissionpacket_pc)
                                            \*packet data loss
                                            /\LossDataStateReRp(p, retransmissionpacket_sequencenumber)
                                            /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                            /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                               \*not arrived
                               \*delete        

SengindRetransmissionPacketRouterRe3(p, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                                                 retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                            /\TimedOut(p, retransmissionpacket_lbTimer)
                            \*arrived
                            /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                        THEN 
                                            /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", retransmissionpacket_pc)
                                            /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                            /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                            \*router buffer
                                            /\router_queue' = router_queue - retransmissionpacket_data[p]
                                            /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                                        ELSE\*router queue overflowing
                                            /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", retransmissionpacket_pc)
                                            \*packet data loss
                                            /\LossDataStateReRp(p, retransmissionpacket_sequencenumber)
                                            /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                            /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                               \*not arrived
                               \*delete        

SengindRetransmissionPacketRouterRe4(p, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                                                 retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                            /\TimedOut(p, retransmissionpacket_lbTimer)
                            \*arrived
                            /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                        THEN 
                                            /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", retransmissionpacket_pc)
                                            /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                            /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                            \*router buffer
                                            /\router_queue' = router_queue - retransmissionpacket_data[p]
                                            /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                                        ELSE\*router queue overflowing
                                            /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", retransmissionpacket_pc)
                                            \*packet data loss
                                            /\LossDataStateReRp(p, retransmissionpacket_sequencenumber)
                                            /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                            /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                               \*not arrived
                               \*delete        

SengindRetransmissionPacketRouterRe5(p, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                                                 retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                            /\TimedOut(p, retransmissionpacket_lbTimer)
                            \*arrived
                            /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                        THEN 
                                            /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", retransmissionpacket_pc)
                                            /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                            /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                            \*router buffer
                                            /\router_queue' = router_queue - retransmissionpacket_data[p]
                                            /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                                        ELSE\*router queue overflowing
                                            /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", retransmissionpacket_pc)
                                            \*packet data loss
                                            /\LossDataStateReRp(p, retransmissionpacket_sequencenumber)
                                            /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                            /\UNCHANGED<<router_queue, 
                                                  mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                               \*not arrived
                               \*delete        

SengindRetransmissionPacketRouterRe6(p, retransmissionpacket_pc, retransmissionpacket_sequencenumber, retransmissionpacket_data,
                                                                 retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                            /\TimedOut(p, retransmissionpacket_lbTimer)
                            \*arrived
                            /\ \/ /\IF (router_queue - retransmissionpacket_data[p] >= 0)
                                        THEN 
                                            /\GoFromTo(p, "SendingToRouterRe", "RoutersRe", retransmissionpacket_pc)
                                            /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                                            /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                                            \*router buffer
                                            /\router_queue' = router_queue - retransmissionpacket_data[p]
                                            /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,      
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                                        ELSE\*router queue overflowing
                                            /\GoFromTo(p, "SendingToRouterRe", "LossDataRe", retransmissionpacket_pc)
                                            \*packet data loss
                                            /\LossDataStateReRp(p, retransmissionpacket_sequencenumber)
                                            /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                            /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, window_size, data,         
                                                  pc, packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_data6,
                                                  now,
                                                  packet_ubTimer, packet_lbTimer,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_lbTimer6,       
                                                  rto, rto_countTimer,
                                                  received_data, received_sequencenumber>>
                               \*not arrived
                               \*delete        

\*packet SendingToRouter      \*Packet
SendingToRouterRe(p)    == /\ \/ /\SendingPacketRouterRe(p)
                              \*RetransmissionPacket1
                              \/ /\SengindRetransmissionPacketRouterRe1(p, rtpacket_pc1, rtpacket_sequencenumber1,
                                                                      rtpacket_data1,  rtpacket_ubTimer1, rtpacket_lbTimer1)
                              \*RetransmissionPacket2
                              \/ /\SengindRetransmissionPacketRouterRe2(p, rtpacket_pc2, rtpacket_sequencenumber2,
                                                                      rtpacket_data2,  rtpacket_ubTimer2, rtpacket_lbTimer2)                                      
                              \*RetransmissionPacket3
                              \/ /\SengindRetransmissionPacketRouterRe3(p, rtpacket_pc3, rtpacket_sequencenumber3,
                                                                      rtpacket_data3,  rtpacket_ubTimer3, rtpacket_lbTimer3)                                      
                              \*RetransmissionPacket4
                              \/ /\SengindRetransmissionPacketRouterRe4(p, rtpacket_pc4, rtpacket_sequencenumber4,
                                                                      rtpacket_data4,  rtpacket_ubTimer4, rtpacket_lbTimer4)
                              \*RetransmissionPacket5
                              \/ /\SengindRetransmissionPacketRouterRe5(p, rtpacket_pc5, rtpacket_sequencenumber5,
                                                                      rtpacket_data5,  rtpacket_ubTimer5, rtpacket_lbTimer5)
                              \*RetransmissionPacket6
                              \/ /\SengindRetransmissionPacketRouterRe6(p, rtpacket_pc6, rtpacket_sequencenumber6,
                                                                      rtpacket_data6,  rtpacket_ubTimer6, rtpacket_lbTimer6)

\*located packet router return
LocatedRouterPacketRe(p) == /\At(p, "RoutersRe", pc) 
                            /\TimedOut(p, packet_lbTimer)
                            /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", pc)
                            /\router_queue' = router_queue + packet_data[p]
                            /\SetTimer(p, packet_ubTimer, 100)
                            /\SetTimer(p, packet_lbTimer, 100)
                            /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                                      packet_sequencenumber, packet_data, 
                                      rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                      rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                      rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                      rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                      rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                      rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                      now,
                                      rtpacket_ubTimer1, rtpacket_lbTimer1,
                                      rtpacket_ubTimer2, rtpacket_lbTimer2,
                                      rtpacket_ubTimer3, rtpacket_lbTimer3,
                                      rtpacket_ubTimer4, rtpacket_lbTimer4,
                                      rtpacket_ubTimer5, rtpacket_lbTimer5,
                                      rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                      rto, rto_countTimer,
                                      received_data, received_sequencenumber>>

\*located retransmission packet router return
LocatedRetransmissionPacketRe1(p,retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                /\At(p, "RoutersRe", retransmissionpacket_pc)
                /\TimedOut(p, retransmissionpacket_lbTimer) 
                /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", retransmissionpacket_pc)
                /\router_queue' = router_queue + retransmissionpacket_data[p]
                /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                          pc, packet_sequencenumber, packet_data, 
                          rtpacket_sequencenumber1, rtpacket_data1, 
                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                          now,
                          packet_ubTimer, packet_lbTimer,
                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                          rto, rto_countTimer,
                          received_data, received_sequencenumber>>

\*located retransmission packet router return
LocatedRetransmissionPacketRe2(p,retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                /\At(p, "RoutersRe", retransmissionpacket_pc)
                /\TimedOut(p, retransmissionpacket_lbTimer) 
                /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", retransmissionpacket_pc)
                /\router_queue' = router_queue + retransmissionpacket_data[p]
                /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                          pc, packet_sequencenumber, packet_data, 
                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                          rtpacket_sequencenumber2, rtpacket_data2, 
                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                          now,
                          packet_ubTimer, packet_lbTimer,
                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                          rto, rto_countTimer,
                          received_data, received_sequencenumber>>

\*located retransmission packet router return
LocatedRetransmissionPacketRe3(p,retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                /\At(p, "RoutersRe", retransmissionpacket_pc)
                /\TimedOut(p, retransmissionpacket_lbTimer) 
                /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", retransmissionpacket_pc)
                /\router_queue' = router_queue + retransmissionpacket_data[p]
                /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                          pc, packet_sequencenumber, packet_data, 
                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                          rtpacket_sequencenumber3, rtpacket_data3, 
                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                          now,
                          packet_ubTimer, packet_lbTimer,
                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                          rto, rto_countTimer,
                          received_data, received_sequencenumber>>

\*located retransmission packet router return
LocatedRetransmissionPacketRe4(p,retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                /\At(p, "RoutersRe", retransmissionpacket_pc)
                /\TimedOut(p, retransmissionpacket_lbTimer) 
                /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", retransmissionpacket_pc)
                /\router_queue' = router_queue + retransmissionpacket_data[p]
                /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                          pc, packet_sequencenumber, packet_data, 
                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                          rtpacket_sequencenumber4, rtpacket_data4, 
                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                          now,
                          packet_ubTimer, packet_lbTimer,
                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                          rtpacket_ubTimer5, rtpacket_lbTimer5,
                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                          rto, rto_countTimer,
                          received_data, received_sequencenumber>>

\*located retransmission packet router return
LocatedRetransmissionPacketRe5(p,retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                /\At(p, "RoutersRe", retransmissionpacket_pc)
                /\TimedOut(p, retransmissionpacket_lbTimer) 
                /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", retransmissionpacket_pc)
                /\router_queue' = router_queue + retransmissionpacket_data[p]
                /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                          pc, packet_sequencenumber, packet_data, 
                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                          rtpacket_sequencenumber5, rtpacket_data5, 
                          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                          now,
                          packet_ubTimer, packet_lbTimer,
                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                          rtpacket_ubTimer6, rtpacket_lbTimer6,       
                          rto, rto_countTimer,
                          received_data, received_sequencenumber>>

\*located retransmission packet router return
LocatedRetransmissionPacketRe6(p,retransmissionpacket_pc, retransmissionpacket_data, retransmissionpacket_lbTimer, retransmissionpacket_ubTimer) == 
                /\At(p, "RoutersRe", retransmissionpacket_pc)
                /\TimedOut(p, retransmissionpacket_lbTimer) 
                /\GoFromTo(p, "RoutersRe", "SendingToSenderRe", retransmissionpacket_pc)
                /\router_queue' = router_queue + retransmissionpacket_data[p]
                /\SetTimer(p, retransmissionpacket_ubTimer, 100)
                /\SetTimer(p, retransmissionpacket_lbTimer, 100)
                /\UNCHANGED<<mss, sequencenumber, window_size, data,         
                          pc, packet_sequencenumber, packet_data, 
                          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                          rtpacket_sequencenumber6, rtpacket_data6,
                          now,
                          packet_ubTimer, packet_lbTimer,
                          rtpacket_ubTimer1, rtpacket_lbTimer1,
                          rtpacket_ubTimer2, rtpacket_lbTimer2,
                          rtpacket_ubTimer3, rtpacket_lbTimer3,
                          rtpacket_ubTimer4, rtpacket_lbTimer4,
                          rtpacket_ubTimer5, rtpacket_lbTimer5,      
                          rto, rto_countTimer,
                          received_data, received_sequencenumber>>

\*located router return   \*packet 
RoutersRe(p)     == /\ \/ /\LocatedRouterPacketRe(p)
                          \*ReTransmissonPacket1
                       \/ /\ LocatedRetransmissionPacketRe1(p,rtpacket_pc1, rtpacket_data1,
                                                        rtpacket_lbTimer1, rtpacket_ubTimer1)
                          \*ReTransmissonPacket2
                       \/ /\ LocatedRetransmissionPacketRe2(p,rtpacket_pc2, rtpacket_data2,
                                                        rtpacket_lbTimer2, rtpacket_ubTimer2)
                          \*ReTransmissonPacket3
                       \/ /\ LocatedRetransmissionPacketRe3(p,rtpacket_pc3, rtpacket_data3,
                                                        rtpacket_lbTimer3, rtpacket_ubTimer3)
                          \*ReTransmissonPacket4
                       \/ /\ LocatedRetransmissionPacketRe4(p,rtpacket_pc4, rtpacket_data4,
                                                        rtpacket_lbTimer4, rtpacket_ubTimer4)
                          \*ReTransmissonPacket5
                       \/ /\ LocatedRetransmissionPacketRe5(p,rtpacket_pc5, rtpacket_data5,
                                                        rtpacket_lbTimer5, rtpacket_ubTimer5)
                          \*ReTransmissonPacket6
                       \/ /\ LocatedRetransmissionPacketRe6(p,rtpacket_pc6, rtpacket_data6,
                                                        rtpacket_lbTimer6, rtpacket_ubTimer6)

\*sending packet sender
SendingPacketSender(s, p) == /\SetTimer(p, packet_ubTimer, 100)
                             /\TimedOut(p, packet_lbTimer)
                             /\SetTimer(p, packet_lbTimer, 100)
                                   \*Success
                             /\ \/ /\GoFromTo(p, "SendingToSenderRe", "Senders", pc)
                                   \*/\packet_sequencenumber' = [packet_sequencenumber EXCEPT![s] = packet_sequencenumber[s] + mss[s]]
                                   /\window_size'         = [window_size EXCEPT![s] = window_size[s]+1]
                                   /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                   /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto,
                                                  received_data, received_sequencenumber>>
                                   \*failure
                                   \*delete

\*all retransmission packet GoTo
AllRetransmissionPacketGoTo(p) == /\GoTo(p,"NoExist", rtpacket_pc1)
                                  /\GoTo(p,"NoExist", rtpacket_pc2)
                                  /\GoTo(p,"NoExist", rtpacket_pc3)
                                  /\GoTo(p,"NoExist", rtpacket_pc4)
                                  /\GoTo(p,"NoExist", rtpacket_pc5)
                                  /\GoTo(p,"NoExist", rtpacket_pc6)

\*sending retransmission packet sender
SendingRetransmissionPacketSender1(s, p, retransmissionpacket_pc, retransmissionpacket_sequencenumber,
                                  retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                   /\SetTimer(p, packet_ubTimer, 100)
                                   /\ResetUBTimer(p,retransmissionpacket_ubTimer)
                                   /\TimedOut(p, retransmissionpacket_lbTimer)
                                   /\SetTimer(p, packet_lbTimer, 100)
                                         \*Success
                                   /\ \/ /\GoFromTo(p, "SendingToSenderRe", "NoExist", retransmissionpacket_pc)
                                         \*packet
                                         /\GoTo(p,"Senders", pc)
                                         \*retransmission packet
                                         /\AllRetransmissionPacketGoTo(p)
                                         \*/\retransmissionpacket_sequencenumber'   = [retransmissionpacket_sequencenumber EXCEPT![p] = retransmissionpacket_sequencenumber[p] + mss[s]]
                                         /\window_size'           = [window_size EXCEPT![s] = window_size[s] + 1]
                                         /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                         /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto,
                                                  received_data, received_sequencenumber>>
                                         \*failure
                                         \*delete

SendingRetransmissionPacketSender2(s, p, retransmissionpacket_pc, retransmissionpacket_sequencenumber,
                                  retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                   /\SetTimer(p, packet_ubTimer, 100)
                                   /\ResetUBTimer(p,retransmissionpacket_ubTimer)
                                   /\TimedOut(p, retransmissionpacket_lbTimer)
                                   /\SetTimer(p, packet_lbTimer, 100)
                                         \*Success
                                   /\ \/ /\GoFromTo(p, "SendingToSenderRe", "NoExist", retransmissionpacket_pc)
                                         \*packet
                                         /\GoTo(p,"Senders", pc)
                                         \*retransmission packet
                                         /\AllRetransmissionPacketGoTo(p)
                                         \*/\retransmissionpacket_sequencenumber'   = [retransmissionpacket_sequencenumber EXCEPT![s] = retransmissionpacket_sequencenumber[s] + mss[s]]
                                         /\window_size'           = [window_size EXCEPT![s] = window_size[s] + 1]
                                         /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                         /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto,
                                                  received_data, received_sequencenumber>>
                                         \*failure
                                         \*delete

SendingRetransmissionPacketSender3(s, p, retransmissionpacket_pc, retransmissionpacket_sequencenumber,
                                  retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                   /\SetTimer(p, packet_ubTimer, 100)
                                   /\ResetUBTimer(p, retransmissionpacket_ubTimer)
                                   /\TimedOut(p, retransmissionpacket_lbTimer)
                                   /\SetTimer(p, packet_lbTimer, 100)
                                         \*Success
                                   /\ \/ /\GoFromTo(p, "SendingToSenderRe", "NoExist", retransmissionpacket_pc)
                                         \*packet
                                         /\GoTo(p,"Senders", pc)
                                         \*retransmission packet
                                         /\AllRetransmissionPacketGoTo(p)
                                         \*/\retransmissionpacket_sequencenumber'   = [retransmissionpacket_sequencenumber EXCEPT![s] = retransmissionpacket_sequencenumber[s] + mss[s]]
                                         /\window_size'           = [window_size EXCEPT![s] = window_size[s] + 1]
                                         /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                         /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto,
                                                  received_data, received_sequencenumber>>
                                         \*failure
                                         \*delete

SendingRetransmissionPacketSender4(s, p, retransmissionpacket_pc, retransmissionpacket_sequencenumber,
                                  retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                   /\SetTimer(p, packet_ubTimer, 100)
                                   /\ResetUBTimer(p,retransmissionpacket_ubTimer)
                                   /\TimedOut(p, retransmissionpacket_lbTimer)
                                   /\SetTimer(p, packet_lbTimer, 100)
                                         \*Success
                                   /\ \/ /\GoFromTo(p, "SendingToSenderRe", "NoExist", retransmissionpacket_pc)
                                         \*packet
                                         /\GoTo(p,"Senders", pc)
                                         \*retransmission packet
                                         /\AllRetransmissionPacketGoTo(p)
                                         \*/\retransmissionpacket_sequencenumber'   = [retransmissionpacket_sequencenumber EXCEPT![s] = retransmissionpacket_sequencenumber[s] + mss[s]]
                                         /\window_size'           = [window_size EXCEPT![s] = window_size[s] + 1]
                                         /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                         /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto,
                                                  received_data, received_sequencenumber>>
                                         \*failure
                                         \*delete

SendingRetransmissionPacketSender5(s, p, retransmissionpacket_pc, retransmissionpacket_sequencenumber,
                                  retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                   /\SetTimer(p, packet_ubTimer, 100)
                                   /\ResetUBTimer(p,retransmissionpacket_ubTimer)
                                   /\TimedOut(p, retransmissionpacket_lbTimer)
                                   /\SetTimer(p, packet_lbTimer, 100)
                                         \*Success
                                   /\ \/ /\GoFromTo(p, "SendingToSenderRe", "NoExist", retransmissionpacket_pc)
                                         \*packet
                                         /\GoTo(p,"Senders", pc)
                                         \*retransmission packet
                                         /\AllRetransmissionPacketGoTo(p)
                                         /\retransmissionpacket_sequencenumber'   = [retransmissionpacket_sequencenumber EXCEPT![s] = retransmissionpacket_sequencenumber[s] + mss[s]]
                                         /\window_size'           = [window_size EXCEPT![s] = window_size[s] + 1]
                                         /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                         /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_lbTimer5,
                                                  rtpacket_ubTimer6, rtpacket_lbTimer6,       
                                                  rto,
                                                  received_data, received_sequencenumber>>
                                         \*failure
                                         \*delete

SendingRetransmissionPacketSender6(s, p, retransmissionpacket_pc, retransmissionpacket_sequencenumber,
                                  retransmissionpacket_ubTimer, retransmissionpacket_lbTimer) == 
                                   /\SetTimer(p, packet_ubTimer, 100)
                                   /\ResetUBTimer(p,retransmissionpacket_ubTimer)
                                   /\TimedOut(p, retransmissionpacket_lbTimer)
                                   /\SetTimer(p, packet_lbTimer, 100)
                                         \*Success
                                   /\ \/ /\GoFromTo(p, "SendingToSenderRe", "NoExist", retransmissionpacket_pc)
                                         \*packet
                                         /\GoTo(p,"Senders", pc)
                                         \*retransmission packet
                                         /\AllRetransmissionPacketGoTo(p)
                                         /\retransmissionpacket_sequencenumber'   = [retransmissionpacket_sequencenumber EXCEPT![s] = retransmissionpacket_sequencenumber[s] + mss[s]]
                                         /\window_size'           = [window_size EXCEPT![s] = window_size[s] + 1]
                                         /\rto_countTimer' = [rto_countTimer EXCEPT![p] = 0]
                                         /\UNCHANGED<<router_queue,
                                                  mss, sequencenumber, data,         
                                                  packet_sequencenumber, packet_data, 
                                                  rtpacket_sequencenumber1, rtpacket_data1, 
                                                  rtpacket_sequencenumber2, rtpacket_data2, 
                                                  rtpacket_sequencenumber3, rtpacket_data3, 
                                                  rtpacket_sequencenumber4, rtpacket_data4, 
                                                  rtpacket_sequencenumber5, rtpacket_data5, 
                                                  rtpacket_sequencenumber6, rtpacket_data6,
                                                  now,
                                                  rtpacket_ubTimer1, rtpacket_lbTimer1,
                                                  rtpacket_ubTimer2, rtpacket_lbTimer2,
                                                  rtpacket_ubTimer3, rtpacket_lbTimer3,
                                                  rtpacket_ubTimer4, rtpacket_lbTimer4,
                                                  rtpacket_ubTimer5, rtpacket_lbTimer5,
                                                  rtpacket_lbTimer5,  
                                                  rto,
                                                  received_data, received_sequencenumber>>
                                         \*failure
                                         \*delete

\*sending sender                   \*send packet receiver
SendingToSenderRe(s,p)    == /\ \/ /\ SendingPacketSender(s, p)
                                   \*ReTransmissonPacket1
                                \/ /\SendingRetransmissionPacketSender1(s, p, rtpacket_pc1, rtpacket_sequencenumber1,
                                                                       rtpacket_ubTimer1, rtpacket_lbTimer1)
                                   \*ReTransmissonPacket2
                                \/ /\SendingRetransmissionPacketSender2(s, p, rtpacket_pc2, rtpacket_sequencenumber2,
                                                                       rtpacket_ubTimer2, rtpacket_lbTimer2)                                   
                                   \*ReTransmissonPacket3
                                \/ /\SendingRetransmissionPacketSender3(s, p, rtpacket_pc3, rtpacket_sequencenumber3,
                                                                       rtpacket_ubTimer3, rtpacket_lbTimer3)
                                   \*ReTransmissonPacket4
                                \/ /\SendingRetransmissionPacketSender4(s, p, rtpacket_pc4, rtpacket_sequencenumber4,
                                                                       rtpacket_ubTimer4, rtpacket_lbTimer4)
                                   \*ReTransmissonPacket5
                                \/ /\SendingRetransmissionPacketSender5(s, p, rtpacket_pc5, rtpacket_sequencenumber5,
                                                                       rtpacket_ubTimer5, rtpacket_lbTimer5)                                   \*ReTransmissonPacket1
                                   \*ReTransmissonPacket6
                                \/ /\SendingRetransmissionPacketSender6(s, p, rtpacket_pc6, rtpacket_sequencenumber6,
                                                                       rtpacket_ubTimer6, rtpacket_lbTimer6) 
                                                              

\*count time [ms]
PosReal == {100}
Tick == 
 \E d \in PosReal:
      \*packet ubtime
      /\ \A p \in Packet: packet_ubTimer[p] >= d
      \* ReTransmisson Packet ubtime
      /\ \A rp \in Packet: rtpacket_ubTimer1[rp] >= d
      /\ \A rp \in Packet: rtpacket_ubTimer2[rp] >= d
      /\ \A rp \in Packet: rtpacket_ubTimer3[rp] >= d
      /\ \A rp \in Packet: rtpacket_ubTimer4[rp] >= d
      /\ \A rp \in Packet: rtpacket_ubTimer5[rp] >= d
      /\ \A rp \in Packet: rtpacket_ubTimer6[rp] >= d
      \*Attacker Packet
      \*/\ \A a \in AttackerPacket: a_ubTimer[a] >= d
      \*tick main
      /\ now' = now + d
      \*packet ubTimer change
      /\ packet_ubTimer' = [p \in Packet |->
                        IF packet_ubTimer[p] = Infinity THEN Infinity
                                                 ELSE packet_ubTimer[p] - d]
      \*retransmissionpacket ubTimer change
      \*retransmission packet 1
      /\ rtpacket_ubTimer1' = [rp \in Packet |->
                           IF rtpacket_ubTimer1[rp] = Infinity THEN Infinity
                                                       ELSE rtpacket_ubTimer1[rp] - d]
      \*retransmission packet 2
      /\ rtpacket_ubTimer2' = [rp \in Packet |->
                           IF rtpacket_ubTimer2[rp] = Infinity THEN Infinity
                                                       ELSE rtpacket_ubTimer2[rp] - d]
      \*retransmission packet 3
      /\ rtpacket_ubTimer3' = [rp \in Packet |->
                           IF rtpacket_ubTimer3[rp] = Infinity THEN Infinity
                                                       ELSE rtpacket_ubTimer3[rp] - d]
      \*retransmission packet 4
      /\ rtpacket_ubTimer4' = [rp \in Packet |->
                           IF rtpacket_ubTimer4[rp] = Infinity THEN Infinity
                                                       ELSE rtpacket_ubTimer4[rp] - d]
      \*retransmission packet 5
      /\ rtpacket_ubTimer5' = [rp \in Packet |->
                           IF rtpacket_ubTimer5[rp] = Infinity THEN Infinity
                                                       ELSE rtpacket_ubTimer5[rp] - d]                                                       
      \*retransmission packet 6
      /\ rtpacket_ubTimer6' = [rp \in Packet |->
                           IF rtpacket_ubTimer6[rp] = Infinity THEN Infinity
                                                       ELSE rtpacket_ubTimer6[rp] - d]
     
     \*attacket ubtimer change
     \*/\ a_ubTimer' = [a \in AttackerPacket |->
     \*                     IF a_ubTimer[a] = Infinity THEN Infinity
     \*                                                ELSE a_ubTimer[a] - d]
      
      \*packet lbtimer change
      /\packet_lbTimer'       = [p \in Packet |-> Max(0,packet_lbTimer[p] - d)]
      \*retransmission packet lbtimer change
      \*retransmission packet1 lbtimer
      /\rtpacket_lbTimer1'    = [rp \in Packet |-> Max(0,rtpacket_lbTimer1[rp] - d)]
      \*retransmission packet2 lbtimer
      /\rtpacket_lbTimer2'    = [rp \in Packet |-> Max(0,rtpacket_lbTimer2[rp] - d)]      
      \*retransmission packet3 lbtimer
      /\rtpacket_lbTimer3'    = [rp \in Packet |-> Max(0,rtpacket_lbTimer3[rp] - d)]
      \*retransmission packet4 lbtimer
      /\rtpacket_lbTimer4'    = [rp \in Packet |-> Max(0,rtpacket_lbTimer4[rp] - d)]      
      \*retransmission packet5 lbtimer
      /\rtpacket_lbTimer5'    = [rp \in Packet |-> Max(0,rtpacket_lbTimer5[rp] - d)]
      \*retransmission packet6 lbtimer
      /\rtpacket_lbTimer6'    = [rp \in Packet |-> Max(0,rtpacket_lbTimer6[rp] - d)]
      \* attacker lbtimer change
      \*/\a_lbTimer'     = [a \in AttackerPacket |-> Max(0,a_lbTimer[a] - d)]

     \*/\rto_countTimer' = [p \in Packet |-> IF (pc[p]#"Senders" /\ pc[p]#"End") THEN rto_countTimer[p] + d
     \*                                                                                 ELSE rto_countTimer[p]]
     /\rto_countTimer' = [p \in Packet |-> IF (pc[p]#"Senders" /\ pc[p] #"End") THEN rto_countTimer[p] + d
                                                                                       ELSE rto_countTimer[p]]
     
     /\ \A p \in Packet: rto[p] > rto_countTimer[p] 
                            
      \* delete UNCHANGED
      /\UNCHANGED <<router_queue,
          mss, sequencenumber, window_size, data,pc, packet_sequencenumber, packet_data, 
          rtpacket_pc1, rtpacket_sequencenumber1, rtpacket_data1, 
          rtpacket_pc2, rtpacket_sequencenumber2, rtpacket_data2, 
          rtpacket_pc3, rtpacket_sequencenumber3, rtpacket_data3, 
          rtpacket_pc4, rtpacket_sequencenumber4, rtpacket_data4, 
          rtpacket_pc5, rtpacket_sequencenumber5, rtpacket_data5, 
          rtpacket_pc6, rtpacket_sequencenumber6, rtpacket_data6,     
          rto, received_data, received_sequencenumber>>
            
SPNext(s,p,r) == \/Senders(s,p)\/SendingToRouter(p)\/Routers(p)
                 \/SendingToReceiver(p)\/Receivers(s,p,r)\/SendingToRouterRe(p)
                 \/RoutersRe(p)\/SendingToSenderRe(s,p)\/ReTransmissionTimeout(s, p)
                 
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
 
Inv1 == /\ \/ /\ \A p \in Packet: pc[p] # "LossData"

Inv2 == /\ \A p \in Packet: pc[p] # "SendingToRouterRe"
        

Inv3 == now # 200

Inv4 == /\ (\E p \in Packet: packet_lbTimer[p] = "SendingToRouter") => (now # 400)

Inv5 == \A p \in Packet: packet_sequencenumber[p] # 2001

Inv6 == \A rp \in Packet: rtpacket_pc1[rp] # "SendingToRouter"

Inv7 == \A p \in Packet: rto_countTimer[p] # 1000

InvEnd == \A p \in Packet: pc[p] # "End"

Inv2000 == \A p \in Packet: rto[p] # 2000

Inv4000 == \A p \in Packet: rto[p] # 4000

Inv8000 == \A p \in Packet: rto[p] # 8000

Inv16000 == \A p \in Packet: rto[p] # 16000

Inv32000 == \A p \in Packet: rto[p] # 32000

Inv64000 == \A p \in Packet: rto[p] # 64000


=============================================================================
\* Modification History
\* Last modified Mon Jan 15 15:14:05 JST 2024 by yamatani
\* Created Mon Jan 15 14:51:34 JST 2024 by yamatani
