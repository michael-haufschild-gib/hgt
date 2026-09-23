import GaloisForLFunctions.HTGeometry.TwoAtomOddLowerReserve

/-!
# Positive lower even block at the coupled two-atom endpoint

For `37/10 ≤ q ≤ 5`, use the existing envelope `U(q)` and its endpoint `z=1/U(q)`.
The operation `twoAtomAffinePart` retains the constant and linear terms of each
existing two-atom moment polynomial, deleting its pure second-pair quadratic term.
With the common Gaussian square and `4*q^(2 : ℕ)` removed, the mass is positive, the
leading two-by-two minor exceeds `100000`, and the leading three-by-three
Hankel determinant exceeds `1000000000000`.

The proof is an exact homogeneous polynomial argument on the closed interval.
Every mixed term is retained before the minors are formed. The estimates concern
the affine lower block; the fourth-coordinate completion and complete source tail
are separate outstanding estimates.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private def sqbEndpointA (u t : ℝ) := 37*u+50*t
private def sqbEndpointB (u t : ℝ) := 10*u+10*t
private def sqbEndpointU (u t : ℝ) := 325*(200*u^(2 : ℕ)+1180*u*t+2501*t^(2 : ℕ))
private def sqbEndpointV (u t : ℝ) := (u+t)^(2 : ℕ)

private def sqbEndpointMoment0 (u t : ℝ) : ℝ :=
  sqbEndpointU u t*(2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)+
    8*sqbEndpointV u t*(2*sqbEndpointA u t-3*sqbEndpointB u t)*
      (8*sqbEndpointA u t-3*sqbEndpointB u t)

private def sqbEndpointMoment1 (u t : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(120*B^(3 : ℕ)-96*A*B^(2 : ℕ)+32*A^(2 : ℕ)*B)+
    sqbEndpointV u t*(2400*B^(3 : ℕ)-10848*A*B^(2 : ℕ)+11200*A^(2 : ℕ)*B-4608*A^(3 : ℕ)))

private def sqbEndpointMoment2 (u t : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(-480*B^(5 : ℕ)+4416*A*B^(4 : ℕ)-2432*A^(2 : ℕ)*B^(3 : ℕ)+768*A^(3 : ℕ)*B^(2 : ℕ))+
    sqbEndpointV u t*(-9600*B^(5 : ℕ)+317568*A*B^(4 : ℕ)-1369600*A^(2 : ℕ)*B^(3 : ℕ)+
      1606272*A^(3 : ℕ)*B^(2 : ℕ)-864000*A^(4 : ℕ)*B+165888*A^(5 : ℕ)))

private def sqbEndpointMoment3 (u t : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(1920*B^(7 : ℕ)-82176*A*B^(6 : ℕ)+253952*A^(2 : ℕ)*B^(5 : ℕ)-
      107520*A^(3 : ℕ)*B^(4 : ℕ)+30720*A^(4 : ℕ)*B^(3 : ℕ))+
    sqbEndpointV u t*(38400*B^(7 : ℕ)-5657088*A*B^(6 : ℕ)+80588800*A^(2 : ℕ)*B^(5 : ℕ)-
      283335168*A^(3 : ℕ)*B^(4 : ℕ)+344716800*A^(4 : ℕ)*B^(3 : ℕ)-206323200*A^(5 : ℕ)*B^(2 : ℕ)+
      60963840*A^(6 : ℕ)*B-5971968*A^(7 : ℕ)))

private def sqbEndpointMoment4 (u t : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(-7680*B^(9 : ℕ)+1360896*A*B^(8 : ℕ)-12388352*A^(2 : ℕ)*B^(7 : ℕ)+
      19611648*A^(3 : ℕ)*B^(6 : ℕ)-6881280*A^(4 : ℕ)*B^(5 : ℕ)+1720320*A^(5 : ℕ)*B^(4 : ℕ))+
    sqbEndpointV u t*(-153600*B^(9 : ℕ)+92817408*A*B^(8 : ℕ)-3465011200*A^(2 : ℕ)*B^(7 : ℕ)+
      29208102912*A^(3 : ℕ)*B^(6 : ℕ)-83216179200*A^(4 : ℕ)*B^(5 : ℕ)+99992137728*A^(5 : ℕ)*B^(4 : ℕ)-
      63139184640*A^(6 : ℕ)*B^(3 : ℕ)+22308784128*A^(7 : ℕ)*B^(2 : ℕ)-3747409920*A^(8 : ℕ)*B+
      214990848*A^(9 : ℕ)))

private theorem sqbEndpointHead_margin {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) :
    0 < sqbEndpointMoment0 u t*sqbEndpointMoment2 u t-sqbEndpointMoment1 u t^(2 : ℕ)-
      100000*(sqbEndpointU u t)^(2 : ℕ)*(sqbEndpointB u t)^(8 : ℕ) := by
  unfold sqbEndpointMoment0 sqbEndpointMoment1 sqbEndpointMoment2
    sqbEndpointA sqbEndpointB sqbEndpointU sqbEndpointV
  dsimp only
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity

private theorem sqbEndpointThreeDet_margin {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) :
    0 < sqbEndpointMoment0 u t*(sqbEndpointMoment2 u t*sqbEndpointMoment4 u t-
        sqbEndpointMoment3 u t^(2 : ℕ))-
      sqbEndpointMoment1 u t*(sqbEndpointMoment1 u t*sqbEndpointMoment4 u t-
        sqbEndpointMoment2 u t*sqbEndpointMoment3 u t)+
      sqbEndpointMoment2 u t*(sqbEndpointMoment1 u t*sqbEndpointMoment3 u t-
        sqbEndpointMoment2 u t^(2 : ℕ))-
      1000000000000*(sqbEndpointU u t)^(3 : ℕ)*(sqbEndpointB u t)^(18 : ℕ) := by
  unfold sqbEndpointMoment0 sqbEndpointMoment1 sqbEndpointMoment2
    sqbEndpointMoment3 sqbEndpointMoment4
    sqbEndpointA sqbEndpointB sqbEndpointU sqbEndpointV
  dsimp only
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity

/-- The constant and linear terms of a quadratic parameter dependence. -/
def twoAtomAffinePart (p : ℝ → ℝ) (z : ℝ) : ℝ :=
  2*p z-(p (2*z)+p 0)/2

/-- Affine retained mass after extracting four times the first scale squared. -/
def twoAtomAffineEvenMoment0 (q z : ℝ) : ℝ :=
  (2*q-3)^(2 : ℕ)+8*z*(2*q-3)*(8*q-3)

/-- First affine signed reflection moment in the common source normalization. -/
def twoAtomAffineEvenMoment1 (q z : ℝ) : ℝ :=
  q*twoAtomAffinePart (twoAtomOddNumerator1 q) z

/-- Second affine signed reflection moment in the common source normalization. -/
def twoAtomAffineEvenMoment2 (q z : ℝ) : ℝ :=
  q*twoAtomAffinePart (twoAtomOddNumerator2 q) z

/-- Third affine signed reflection moment in the common source normalization. -/
def twoAtomAffineEvenMoment3 (q z : ℝ) : ℝ :=
  q*twoAtomAffinePart (twoAtomOddNumerator3 q) z

/-- Fourth affine signed reflection moment in the common source normalization. -/
def twoAtomAffineEvenMoment4 (q z : ℝ) : ℝ :=
  q*twoAtomAffinePart (twoAtomOddNumerator4 q) z

private theorem affine_scale_identities (q : ℝ) :
    sqbEndpointA (50-10*q) (10*q-37) = 130*q ∧
    sqbEndpointB (50-10*q) (10*q-37) = 130 ∧
    sqbEndpointU (50-10*q) (10*q-37) = 169*twoAtomLowerEnvelope q ∧
    sqbEndpointV (50-10*q) (10*q-37) = 169 := by
  unfold sqbEndpointA sqbEndpointB sqbEndpointU sqbEndpointV twoAtomLowerEnvelope
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private theorem affine_envelope_pos {q : ℝ} (hq : 37/10 ≤ q) :
    0 < twoAtomLowerEnvelope q := by
  have h : 0 ≤ q-37/10 := by linarith
  unfold twoAtomLowerEnvelope
  positivity

private theorem affine_moment0_hom (q : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment0 (50-10*q) (10*q-37) =
      (169*twoAtomLowerEnvelope q)*130^(2 : ℕ)*
        twoAtomAffineEvenMoment0 q (1/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment0
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment0
  field_simp [hU]

private theorem affine_moment1_hom (q : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment1 (50-10*q) (10*q-37) =
      (169*twoAtomLowerEnvelope q)*130^(4 : ℕ)*
        twoAtomAffineEvenMoment1 q (1/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment1
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment1 twoAtomAffinePart twoAtomOddNumerator1
  field_simp [hU]
  ring

private theorem affine_moment2_hom (q : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment2 (50-10*q) (10*q-37) =
      (169*twoAtomLowerEnvelope q)*130^(6 : ℕ)*
        twoAtomAffineEvenMoment2 q (1/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment2
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment2 twoAtomAffinePart twoAtomOddNumerator2
  field_simp [hU]
  ring

private theorem affine_moment3_hom (q : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment3 (50-10*q) (10*q-37) =
      (169*twoAtomLowerEnvelope q)*130^(8 : ℕ)*
        twoAtomAffineEvenMoment3 q (1/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment3
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment3 twoAtomAffinePart twoAtomOddNumerator3
  field_simp [hU]
  ring

private theorem affine_moment4_hom (q : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment4 (50-10*q) (10*q-37) =
      (169*twoAtomLowerEnvelope q)*130^(10 : ℕ)*
        twoAtomAffineEvenMoment4 q (1/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment4
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment4 twoAtomAffinePart twoAtomOddNumerator4
  field_simp [hU]
  ring

/-- Strict affine endpoint mass throughout the closed lower-middle interval. -/
theorem twoAtomAffineEvenMass_pos {q : ℝ} (hq : 37/10 ≤ q) :
    0 < twoAtomAffineEvenMoment0 q (1/twoAtomLowerEnvelope q) := by
  have hd : 0 < 2*q-3 := by linarith
  have hr : 0 < 8*q-3 := by linarith
  have hU := affine_envelope_pos hq
  unfold twoAtomAffineEvenMoment0
  positivity

/-- The leading affine even minor exceeds one hundred thousand on the closed lower middle. -/
theorem twoAtomAffineEvenHead_lower {q : ℝ} (hq : 37/10 ≤ q) (hqu : q ≤ 5) :
    100000 < twoAtomAffineEvenMoment0 q (1/twoAtomLowerEnvelope q)*
        twoAtomAffineEvenMoment2 q (1/twoAtomLowerEnvelope q)-
      twoAtomAffineEvenMoment1 q (1/twoAtomLowerEnvelope q)^(2 : ℕ) := by
  have hU := affine_envelope_pos hq
  have h := sqbEndpointHead_margin (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) (by linarith)
  rw [affine_moment0_hom q hU.ne',affine_moment1_hom q hU.ne',
    affine_moment2_hom q hU.ne'] at h
  have he : 0 < (169*twoAtomLowerEnvelope q)^(2 : ℕ)*130^(8 : ℕ)*
      (twoAtomAffineEvenMoment0 q (1/twoAtomLowerEnvelope q)*
        twoAtomAffineEvenMoment2 q (1/twoAtomLowerEnvelope q)-
        twoAtomAffineEvenMoment1 q (1/twoAtomLowerEnvelope q)^(2 : ℕ)-100000) := by
    rw [(affine_scale_identities q).2.2.1,(affine_scale_identities q).2.1] at h
    convert h using 1
    ring
  have hh := (mul_pos_iff_of_pos_left (by positivity)).mp he
  linarith only [hh]

/-- The full leading affine even determinant exceeds one trillion on the closed lower middle. -/
theorem twoAtomAffineEvenThreeDet_lower {q : ℝ} (hq : 37/10 ≤ q) (hqu : q ≤ 5) :
    1000000000000 < HilbertMetric.signedEvenHankelThreeDet
      (twoAtomAffineEvenMoment0 q (1/twoAtomLowerEnvelope q))
      (twoAtomAffineEvenMoment1 q (1/twoAtomLowerEnvelope q))
      (twoAtomAffineEvenMoment2 q (1/twoAtomLowerEnvelope q))
      (twoAtomAffineEvenMoment3 q (1/twoAtomLowerEnvelope q))
      (twoAtomAffineEvenMoment4 q (1/twoAtomLowerEnvelope q)) := by
  have hU := affine_envelope_pos hq
  have h := sqbEndpointThreeDet_margin (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) (by linarith)
  rw [affine_moment0_hom q hU.ne',affine_moment1_hom q hU.ne',
    affine_moment2_hom q hU.ne',affine_moment3_hom q hU.ne',
    affine_moment4_hom q hU.ne'] at h
  have he : 0 < (169*twoAtomLowerEnvelope q)^(3 : ℕ)*130^(18 : ℕ)*
      (HilbertMetric.signedEvenHankelThreeDet
        (twoAtomAffineEvenMoment0 q (1/twoAtomLowerEnvelope q))
        (twoAtomAffineEvenMoment1 q (1/twoAtomLowerEnvelope q))
        (twoAtomAffineEvenMoment2 q (1/twoAtomLowerEnvelope q))
        (twoAtomAffineEvenMoment3 q (1/twoAtomLowerEnvelope q))
        (twoAtomAffineEvenMoment4 q (1/twoAtomLowerEnvelope q))-1000000000000) := by
    rw [(affine_scale_identities q).2.2.1,(affine_scale_identities q).2.1] at h
    convert h using 1
    unfold HilbertMetric.signedEvenHankelThreeDet
    ring
  have hh := (mul_pos_iff_of_pos_left (by positivity)).mp he
  linarith only [hh]

end
end HTGeometry
