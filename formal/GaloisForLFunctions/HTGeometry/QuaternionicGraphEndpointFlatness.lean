import GaloisForLFunctions.HTGeometry.QuaternionicActualityGraphLock

/-!
# Canonically flat transport of event-selected quaternionic graph frames

For pointed unit quaternions `q` and `r`, the right factor

`star r * q`

canonically sends `q` to `r` under the algebraic `Spin(4)` pair action.  These endpoint transports
form a strict flat cocycle: they compose through intermediate points and every closed triangle has
identity holonomy.

The file also classifies every unit pair element mapping `q` to `r`.  It factors uniquely into the
canonical endpoint transport followed by one element of the graph stabilizer selected by `q`.
Thus endpoint directions alone carry no nontrivial loop holonomy; any such holonomy requires extra
transporter data.

These are unconditional quaternion identities.  No physical actualization, connection, spacetime,
gravity, Higgs field, or gauge force is assumed.
-/

open scoped Quaternion RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Canonical right-factor transport from pointed unit quaternion `q` to `r`. -/
def quaternionGraphEndpointTransport
    (q r : EventQuaternion) : EventQuaternion :=
  star r * q

/-- Canonical endpoint transport is unit. -/
theorem quaternionGraphEndpointTransport_unit
    (q r : EventQuaternion)
    (hq : Quaternion.normSq q = 1)
    (hr : Quaternion.normSq r = 1) :
    Quaternion.normSq (quaternionGraphEndpointTransport q r) = 1 := by
  rw [quaternionGraphEndpointTransport, map_mul, Quaternion.normSq_star, hq, hr]
  simp

/-- Canonical endpoint transport sends its source point to its target point. -/
theorem spinFourPairAction_endpointTransport
    (q r : EventQuaternion)
    (hq : Quaternion.normSq q = 1) :
    spinFourPairAction 1 (quaternionGraphEndpointTransport q r) q = r := by
  simp only [spinFourPairAction, quaternionGraphEndpointTransport, one_mul, star_mul, star_star]
  rw [← mul_assoc, Quaternion.self_mul_star, hq]
  simp

/-- Endpoint transport at one point is the identity. -/
theorem quaternionGraphEndpointTransport_self
    (q : EventQuaternion)
    (hq : Quaternion.normSq q = 1) :
    quaternionGraphEndpointTransport q q = 1 := by
  rw [quaternionGraphEndpointTransport, Quaternion.star_mul_self, hq]
  rfl

/-- Reversing endpoint transport takes the quaternionic adjoint. -/
theorem quaternionGraphEndpointTransport_reverse
    (q r : EventQuaternion) :
    quaternionGraphEndpointTransport r q =
      star (quaternionGraphEndpointTransport q r) := by
  simp [quaternionGraphEndpointTransport, star_mul]

/-- Canonical endpoint transports compose as a strict pair-groupoid cocycle. -/
theorem quaternionGraphEndpointTransport_trans
    (q r s : EventQuaternion)
    (hr : Quaternion.normSq r = 1) :
    quaternionGraphEndpointTransport r s *
        quaternionGraphEndpointTransport q r =
      quaternionGraphEndpointTransport q s := by
  simp only [quaternionGraphEndpointTransport]
  calc
    (star s * r) * (star r * q) =
        star s * (r * star r) * q := by noncomm_ring
    _ = star s * q := by
      rw [Quaternion.self_mul_star, hr]
      simp

/-- Every endpoint triangle has trivial canonical holonomy. -/
theorem quaternionGraphEndpointTransport_triangle
    (q r s : EventQuaternion)
    (hq : Quaternion.normSq q = 1)
    (hr : Quaternion.normSq r = 1)
    (hs : Quaternion.normSq s = 1) :
    quaternionGraphEndpointTransport s q *
          quaternionGraphEndpointTransport r s *
        quaternionGraphEndpointTransport q r = 1 := by
  rw [quaternionGraphEndpointTransport_trans r s q hs,
    quaternionGraphEndpointTransport_trans q r q hr,
    quaternionGraphEndpointTransport_self q hq]

/-- Unit pair elements mapping `q` to `r` are exactly the endpoint graph transporters. -/
theorem spinFourPairAction_eq_iff_endpointGraph
    (u v q r : EventQuaternion)
    (hu : Quaternion.normSq u = 1)
    (hv : Quaternion.normSq v = 1)
    (hq : Quaternion.normSq q = 1)
    (hr : Quaternion.normSq r = 1) :
    spinFourPairAction u v q = r ↔ v = star r * u * q := by
  constructor
  · intro hmap
    have hright := congrArg (fun x : EventQuaternion => x * v) hmap
    have huv : u * q = r * v := by
      simpa [spinFourPairAction, mul_assoc, Quaternion.star_mul_self, hv] using hright
    calc
      v = (star r * r) * v := by rw [Quaternion.star_mul_self, hr]; simp
      _ = star r * (r * v) := by rw [mul_assoc]
      _ = star r * (u * q) := by rw [huv]
      _ = star r * u * q := by rw [mul_assoc]
  · rintro rfl
    simp only [spinFourPairAction, star_mul, star_star]
    calc
      u * q * (star q * (star u * r)) =
          u * (q * star q) * star u * r := by noncomm_ring
      _ = r := by
        rw [Quaternion.self_mul_star, hq]
        norm_num
        rw [Quaternion.self_mul_star, hu]
        simp

/-- Endpoint transport followed by the source graph partner is the general right factor. -/
theorem quaternionGraphEndpointTransport_mul_graphPartner
    (u q r : EventQuaternion)
    (hq : Quaternion.normSq q = 1) :
    quaternionGraphEndpointTransport q r * (star q * u * q) =
      star r * u * q := by
  simp only [quaternionGraphEndpointTransport]
  calc
    (star r * q) * (star q * u * q) =
        star r * (q * star q) * u * q := by noncomm_ring
    _ = star r * u * q := by
      rw [Quaternion.self_mul_star, hq]
      simp

/--
Every unit pair transporter is canonical flat endpoint transport times one source-stabilizer
element.
-/
theorem spinFourPairAction_eq_iff_endpoint_mul_stabilizer
    (u v q r : EventQuaternion)
    (hu : Quaternion.normSq u = 1)
    (hv : Quaternion.normSq v = 1)
    (hq : Quaternion.normSq q = 1)
    (hr : Quaternion.normSq r = 1) :
    spinFourPairAction u v q = r ↔
      v = quaternionGraphEndpointTransport q r * (star q * u * q) := by
  rw [spinFourPairAction_eq_iff_endpointGraph u v q r hu hv hq hr,
    quaternionGraphEndpointTransport_mul_graphPartner u q r hq]

/-- Flat endpoint transport conjugates the source graph partner to the target graph partner. -/
theorem quaternionGraphEndpointTransport_conjugates_graphPartner
    (u q r : EventQuaternion)
    (hq : Quaternion.normSq q = 1) :
    quaternionGraphEndpointTransport q r * (star q * u * q) *
        star (quaternionGraphEndpointTransport q r) =
      star r * u * r := by
  simp only [quaternionGraphEndpointTransport, star_mul, star_star]
  calc
    (star r * q) * (star q * u * q) * (star q * r) =
        star r * (q * star q) * u * (q * star q) * r := by noncomm_ring
    _ = star r * u * r := by
      rw [Quaternion.self_mul_star, hq]
      simp

end GaloisForLFunctions.HTGeometry
