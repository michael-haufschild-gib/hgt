import GaloisForLFunctions.HTGeometry.TwoAtomAffineEvenHead
import GaloisForLFunctions.HTGeometry.HankelFourDeterminant

/-!
# Corrected affine even fourth determinant on the inner interval

On `37/10 ≤ q ≤ 5`, the complete-source correction admits the stronger lower
coefficient `11/2-q`. With this coefficient and fixed multiplier `10^(12 : ℕ)`, the
affine endpoint fourth determinant exceeds `10^(20 : ℕ)`. The proof retains the
mixed-pair moments through order twelve and uses exact homogeneous polynomial
identities. Literal source identification and complete-tail absorption are
separate statements; this module proves the finite polynomial margin.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
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


private def sqbEndpointMoment5 (u t : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(30720*B^(11 : ℕ)-21958656*A*B^(10 : ℕ)+500252672*A^(2 : ℕ)*B^(9 : ℕ)-
      1924055040*A^(3 : ℕ)*B^(8 : ℕ)+1899233280*A^(4 : ℕ)*B^(7 : ℕ)-578027520*A^(5 : ℕ)*B^(6 : ℕ)+123863040*A^(6 : ℕ)*B^(5 : ℕ))+
    sqbEndpointV u t*(614400*B^(11 : ℕ)-1494294528*A*B^(10 : ℕ)+134014566400*A^(2 : ℕ)*B^(9 : ℕ)-
      2350982012928*A^(3 : ℕ)*B^(8 : ℕ)+13476986265600*A^(4 : ℕ)*B^(7 : ℕ)-32021436211200*A^(5 : ℕ)*B^(6 : ℕ)+
      36948979630080*A^(6 : ℕ)*B^(5 : ℕ)-23901460217856*A^(7 : ℕ)*B^(4 : ℕ)+9261775872000*A^(8 : ℕ)*B^(3 : ℕ)-
      2004305928192*A^(9 : ℕ)*B^(2 : ℕ)+208003645440*A^(10 : ℕ)*B-7739670528*A^(11 : ℕ)))

private def sqbEndpointMoment6 (u t : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  sqbEndpointU u t*(-122880*A*B^(13 : ℕ)+352075776*A^(2 : ℕ)*B^(12 : ℕ)-18886787072*A^(3 : ℕ)*B^(11 : ℕ)+
    150752329728*A^(4 : ℕ)*B^(10 : ℕ)-320229212160*A^(5 : ℕ)*B^(9 : ℕ)+221632266240*A^(6 : ℕ)*B^(8 : ℕ)-
    59949711360*A^(7 : ℕ)*B^(7 : ℕ)+10899947520*A^(8 : ℕ)*B^(6 : ℕ))+
  sqbEndpointV u t*(-2457600*A*B^(13 : ℕ)+23945576448*A^(2 : ℕ)*B^(12 : ℕ)-4973923532800*A^(3 : ℕ)*B^(11 : ℕ)+
    169169423204352*A^(4 : ℕ)*B^(10 : ℕ)-1766855919206400*A^(5 : ℕ)*B^(9 : ℕ)+7517668254547968*A^(6 : ℕ)*B^(8 : ℕ)-
    15294052901191680*A^(7 : ℕ)*B^(7 : ℕ)+16720020540850176*A^(8 : ℕ)*B^(6 : ℕ)-
    10861074754928640*A^(9 : ℕ)*B^(5 : ℕ)+4434116081319936*A^(10 : ℕ)*B^(4 : ℕ)-
    1107009375436800*A^(11 : ℕ)*B^(3 : ℕ)+155081713287168*A^(12 : ℕ)*B^(2 : ℕ)-
    10738792857600*A^(13 : ℕ)*B+278628139008*A^(14 : ℕ))

private theorem sqbEndpointFourDet_affineCompensation_margin {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) :
    0 < GaloisForLFunctions.HTGeometry.hankelFourDet (sqbEndpointMoment0 u t) (sqbEndpointMoment1 u t)
      (sqbEndpointMoment2 u t) (sqbEndpointMoment3 u t)
      (sqbEndpointMoment4 u t) (sqbEndpointMoment5 u t)
      (sqbEndpointMoment6 u t+
        500000000000*sqbEndpointU u t*(sqbEndpointB u t)^(11 : ℕ)*
          (11*sqbEndpointB u t-2*sqbEndpointA u t)*
          (2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ))-
      100000000000000000000*(sqbEndpointU u t)^(4 : ℕ)*(sqbEndpointB u t)^(32 : ℕ) := by
  unfold GaloisForLFunctions.HTGeometry.hankelFourDet sqbEndpointMoment0 sqbEndpointMoment1 sqbEndpointMoment2
    sqbEndpointMoment3 sqbEndpointMoment4 sqbEndpointMoment5 sqbEndpointMoment6
    sqbEndpointA sqbEndpointB sqbEndpointU sqbEndpointV
  dsimp only
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity

/-- Fifth affine even moment, retaining both ordered unequal-atom pairs. -/
def twoAtomAffineEvenMoment5 (q z : ℝ) : ℝ :=
  q*twoAtomAffinePart (twoAtomOddNumerator5 q) z

/-- Sixth affine even moment in the same Gaussian and scale normalization. -/
def twoAtomAffineEvenMoment6 (q z : ℝ) : ℝ :=
  -122880*q+352075776*q^(2 : ℕ)-18886787072*q^(3 : ℕ)+150752329728*q^(4 : ℕ)-
    320229212160*q^(5 : ℕ)+221632266240*q^(6 : ℕ)-59949711360*q^(7 : ℕ)+10899947520*q^(8 : ℕ)+
  z*(-2457600*q+23945576448*q^(2 : ℕ)-4973923532800*q^(3 : ℕ)+169169423204352*q^(4 : ℕ)-
    1766855919206400*q^(5 : ℕ)+7517668254547968*q^(6 : ℕ)-15294052901191680*q^(7 : ℕ)+
    16720020540850176*q^(8 : ℕ)-10861074754928640*q^(9 : ℕ)+4434116081319936*q^(10 : ℕ)-
    1107009375436800*q^(11 : ℕ)+155081713287168*q^(12 : ℕ)-10738792857600*q^(13 : ℕ)+
    278628139008*q^(14 : ℕ))

/-- Affine fourth determinant with the scale-dependent lower complete-source correction. -/
def twoAtomAffineEvenFourCorrectedDet (q z : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.hankelFourDet
    (twoAtomAffineEvenMoment0 q z) (twoAtomAffineEvenMoment1 q z)
    (twoAtomAffineEvenMoment2 q z) (twoAtomAffineEvenMoment3 q z)
    (twoAtomAffineEvenMoment4 q z) (twoAtomAffineEvenMoment5 q z)
    (twoAtomAffineEvenMoment6 q z+1000000000000*(11/2-q)*(2*q-3)^(2 : ℕ))
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


private theorem affine_moment5_hom (q : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment5 (50-10*q) (10*q-37) =
      (169*twoAtomLowerEnvelope q)*130^(12 : ℕ)*
        twoAtomAffineEvenMoment5 q (1/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment5
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment5 twoAtomAffinePart twoAtomOddNumerator5
  field_simp [hU]
  ring

private theorem affine_moment6_hom (q : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment6 (50-10*q) (10*q-37) =
      (169*twoAtomLowerEnvelope q)*130^(14 : ℕ)*
        twoAtomAffineEvenMoment6 q (1/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment6
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment6
  field_simp [hU]

/-- The corrected affine fourth determinant has an explicit strict margin on the closed inner interval. -/
theorem twoAtomAffineEvenFourCorrectedDet_lower {q : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) :
    100000000000000000000 < twoAtomAffineEvenFourCorrectedDet q (1/twoAtomLowerEnvelope q) := by
  have hU := affine_envelope_pos hq
  have h := sqbEndpointFourDet_affineCompensation_margin (u:=50-10*q) (t:=10*q-37)
    (by linarith) (by linarith) (by linarith)
  rw [affine_moment0_hom q hU.ne',affine_moment1_hom q hU.ne',
    affine_moment2_hom q hU.ne',affine_moment3_hom q hU.ne',
    affine_moment4_hom q hU.ne',affine_moment5_hom q hU.ne',
    affine_moment6_hom q hU.ne'] at h
  rw [(affine_scale_identities q).1,(affine_scale_identities q).2.1,
    (affine_scale_identities q).2.2.1] at h
  have he : 0 < (169*twoAtomLowerEnvelope q)^(4 : ℕ)*130^(32 : ℕ)*
      (twoAtomAffineEvenFourCorrectedDet q (1/twoAtomLowerEnvelope q)-
        100000000000000000000) := by
    convert h using 1
    unfold twoAtomAffineEvenFourCorrectedDet GaloisForLFunctions.HTGeometry.hankelFourDet
    ring
  have hh := (mul_pos_iff_of_pos_left (by positivity)).mp he
  linarith only [hh]

end
end HTGeometry
