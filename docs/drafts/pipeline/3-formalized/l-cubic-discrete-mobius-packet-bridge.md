# Route L cubic Möbius energy as a discrete packet norm

- **ID:** L-CUBIC-DISCRETE-PACKET-BRIDGE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Module:** [MobiusReciprocalDiscretePacketBridge.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusReciprocalDiscretePacketBridge.lean)
- **Paper extension:** [All-order identity and finite packet horizon](route%20l/l-discrete-mobius-packet-sobolev.md)

For every finite cutoff `N` and `delta≥0`, the module proves that the literal cubic Route L source packet is `(b_k-2b_(k+2)+b_(k+4))/16`, where `b_k` is the original order-one Möbius packet. The theorem `routeLCubicEnergy_eq_packetSecondDifference` identifies the full finite coupled-order energy with its positive weighted square sum. It depends on the already formalized generic Gamma--Hankel packet expansion and the exact integer-numerator Route L kernel; it introduces no new premise about Möbius cancellation.

The module is imported by `GaloisForLFunctions/RHTower.lean`. Targeted `lake --old build GaloisForLFunctions.RHTower.MobiusReciprocalDiscretePacketBridge` completed successfully. Repository lint currently reports a separate module, `ThetaCuspHawkingBMPWCrossClockLogIdentity`, as unreachable from the umbrella; this module's own import is present. The cutoff-uniform bound of the square sum, which would feed the closed Route L RH receiver, remains open.
