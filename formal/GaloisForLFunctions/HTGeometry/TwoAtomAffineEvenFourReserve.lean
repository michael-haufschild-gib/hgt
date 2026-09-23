import GaloisForLFunctions.HTGeometry.TwoAtomAffineEvenFour

/-! # Explicit diagonal reserve inside the corrected affine fourth matrix -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
private def sqbEndpointA (u t : ℝ) := 37*u+50*t
private def sqbEndpointB (u t : ℝ) := 10*u+10*t
private def sqbEndpointU (u t : ℝ) := 325*(200*u^(2 : ℕ)+1180*u*t+2501*t^(2 : ℕ))
private def sqbEndpointV (u t : ℝ) := (u+t)^(2 : ℕ)

private def sqbEndpointMoment0 (u t r : ℝ) : ℝ :=
  sqbEndpointU u t*(2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)+
    8*(r*sqbEndpointV u t)*(2*sqbEndpointA u t-3*sqbEndpointB u t)*
      (8*sqbEndpointA u t-3*sqbEndpointB u t)

private def sqbEndpointMoment1 (u t r : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(120*B^(3 : ℕ)-96*A*B^(2 : ℕ)+32*A^(2 : ℕ)*B)+
    (r*sqbEndpointV u t)*(2400*B^(3 : ℕ)-10848*A*B^(2 : ℕ)+11200*A^(2 : ℕ)*B-4608*A^(3 : ℕ)))

private def sqbEndpointMoment2 (u t r : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(-480*B^(5 : ℕ)+4416*A*B^(4 : ℕ)-2432*A^(2 : ℕ)*B^(3 : ℕ)+768*A^(3 : ℕ)*B^(2 : ℕ))+
    (r*sqbEndpointV u t)*(-9600*B^(5 : ℕ)+317568*A*B^(4 : ℕ)-1369600*A^(2 : ℕ)*B^(3 : ℕ)+
      1606272*A^(3 : ℕ)*B^(2 : ℕ)-864000*A^(4 : ℕ)*B+165888*A^(5 : ℕ)))

private def sqbEndpointMoment3 (u t r : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(1920*B^(7 : ℕ)-82176*A*B^(6 : ℕ)+253952*A^(2 : ℕ)*B^(5 : ℕ)-
      107520*A^(3 : ℕ)*B^(4 : ℕ)+30720*A^(4 : ℕ)*B^(3 : ℕ))+
    (r*sqbEndpointV u t)*(38400*B^(7 : ℕ)-5657088*A*B^(6 : ℕ)+80588800*A^(2 : ℕ)*B^(5 : ℕ)-
      283335168*A^(3 : ℕ)*B^(4 : ℕ)+344716800*A^(4 : ℕ)*B^(3 : ℕ)-206323200*A^(5 : ℕ)*B^(2 : ℕ)+
      60963840*A^(6 : ℕ)*B-5971968*A^(7 : ℕ)))

private def sqbEndpointMoment4 (u t r : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(-7680*B^(9 : ℕ)+1360896*A*B^(8 : ℕ)-12388352*A^(2 : ℕ)*B^(7 : ℕ)+
      19611648*A^(3 : ℕ)*B^(6 : ℕ)-6881280*A^(4 : ℕ)*B^(5 : ℕ)+1720320*A^(5 : ℕ)*B^(4 : ℕ))+
    (r*sqbEndpointV u t)*(-153600*B^(9 : ℕ)+92817408*A*B^(8 : ℕ)-3465011200*A^(2 : ℕ)*B^(7 : ℕ)+
      29208102912*A^(3 : ℕ)*B^(6 : ℕ)-83216179200*A^(4 : ℕ)*B^(5 : ℕ)+99992137728*A^(5 : ℕ)*B^(4 : ℕ)-
      63139184640*A^(6 : ℕ)*B^(3 : ℕ)+22308784128*A^(7 : ℕ)*B^(2 : ℕ)-3747409920*A^(8 : ℕ)*B+
      214990848*A^(9 : ℕ)))


private def sqbEndpointMoment5 (u t r : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  A*(sqbEndpointU u t*(30720*B^(11 : ℕ)-21958656*A*B^(10 : ℕ)+500252672*A^(2 : ℕ)*B^(9 : ℕ)-
      1924055040*A^(3 : ℕ)*B^(8 : ℕ)+1899233280*A^(4 : ℕ)*B^(7 : ℕ)-578027520*A^(5 : ℕ)*B^(6 : ℕ)+123863040*A^(6 : ℕ)*B^(5 : ℕ))+
    (r*sqbEndpointV u t)*(614400*B^(11 : ℕ)-1494294528*A*B^(10 : ℕ)+134014566400*A^(2 : ℕ)*B^(9 : ℕ)-
      2350982012928*A^(3 : ℕ)*B^(8 : ℕ)+13476986265600*A^(4 : ℕ)*B^(7 : ℕ)-32021436211200*A^(5 : ℕ)*B^(6 : ℕ)+
      36948979630080*A^(6 : ℕ)*B^(5 : ℕ)-23901460217856*A^(7 : ℕ)*B^(4 : ℕ)+9261775872000*A^(8 : ℕ)*B^(3 : ℕ)-
      2004305928192*A^(9 : ℕ)*B^(2 : ℕ)+208003645440*A^(10 : ℕ)*B-7739670528*A^(11 : ℕ)))

private def sqbEndpointMoment6 (u t r : ℝ) : ℝ :=
  let A := sqbEndpointA u t; let B := sqbEndpointB u t
  sqbEndpointU u t*(-122880*A*B^(13 : ℕ)+352075776*A^(2 : ℕ)*B^(12 : ℕ)-18886787072*A^(3 : ℕ)*B^(11 : ℕ)+
    150752329728*A^(4 : ℕ)*B^(10 : ℕ)-320229212160*A^(5 : ℕ)*B^(9 : ℕ)+221632266240*A^(6 : ℕ)*B^(8 : ℕ)-
    59949711360*A^(7 : ℕ)*B^(7 : ℕ)+10899947520*A^(8 : ℕ)*B^(6 : ℕ))+
  (r*sqbEndpointV u t)*(-2457600*A*B^(13 : ℕ)+23945576448*A^(2 : ℕ)*B^(12 : ℕ)-4973923532800*A^(3 : ℕ)*B^(11 : ℕ)+
    169169423204352*A^(4 : ℕ)*B^(10 : ℕ)-1766855919206400*A^(5 : ℕ)*B^(9 : ℕ)+7517668254547968*A^(6 : ℕ)*B^(8 : ℕ)-
    15294052901191680*A^(7 : ℕ)*B^(7 : ℕ)+16720020540850176*A^(8 : ℕ)*B^(6 : ℕ)-
    10861074754928640*A^(9 : ℕ)*B^(5 : ℕ)+4434116081319936*A^(10 : ℕ)*B^(4 : ℕ)-
    1107009375436800*A^(11 : ℕ)*B^(3 : ℕ)+155081713287168*A^(12 : ℕ)*B^(2 : ℕ)-
    10738792857600*A^(13 : ℕ)*B+278628139008*A^(14 : ℕ))

private def detSym4 (a b c d e f g h i j : ℝ) :=
  (a*e*h-a*f^(2 : ℕ)-b^(2 : ℕ)*h+2*b*c*f-c^(2 : ℕ)*e)*j -
    ((e*h-f^(2 : ℕ))*d^(2 : ℕ)+2*(c*f-b*h)*d*g+2*(b*f-c*e)*d*i+
      (a*h-c^(2 : ℕ))*g^(2 : ℕ)+2*(b*c-a*f)*g*i+(a*e-b^(2 : ℕ))*i^(2 : ℕ))

private def reserve0 (u t : ℝ) : ℝ :=
  (1/1000000)*sqbEndpointU u t*(2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)
private def reserve1 (u t : ℝ) : ℝ :=
  (1/10000)*sqbEndpointU u t*(2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)*
    (8*sqbEndpointA u t)^(2 : ℕ)*(sqbEndpointB u t)^(2 : ℕ)
private def reserve2 (u t : ℝ) : ℝ :=
  (1/10)*sqbEndpointU u t*(2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)*
    (8*sqbEndpointA u t)^(4 : ℕ)*(sqbEndpointB u t)^(4 : ℕ)
private def reserve3 (u t : ℝ) : ℝ :=
  sqbEndpointU u t*(2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)*
    (8*sqbEndpointA u t)^(6 : ℕ)*(sqbEndpointB u t)^(4 : ℕ)*
    (500*(5*sqbEndpointB u t-sqbEndpointA u t)^(2 : ℕ)+(sqbEndpointB u t)^(2 : ℕ))


private theorem reserved_mass_0_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) : 0 < sqbEndpointMoment0 u t 0-reserve0 u t := by
  simp only [sqbEndpointMoment0, reserve0,
    sqbEndpointA, sqbEndpointB, sqbEndpointU, sqbEndpointV]
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity

private theorem reserved_head_0_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) : 0 < (sqbEndpointMoment0 u t 0-reserve0 u t)*(sqbEndpointMoment2 u t 0-reserve1 u t)-(sqbEndpointMoment1 u t 0)^(2 : ℕ) := by
  simp only [sqbEndpointMoment0, sqbEndpointMoment1, sqbEndpointMoment2,
    reserve0, reserve1,
    sqbEndpointA, sqbEndpointB, sqbEndpointU, sqbEndpointV]
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity

private theorem reserved_three_0_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) : 0 < (sqbEndpointMoment0 u t 0-reserve0 u t)*(sqbEndpointMoment2 u t 0-reserve1 u t)*(sqbEndpointMoment4 u t 0-reserve2 u t)-(sqbEndpointMoment0 u t 0-reserve0 u t)*(sqbEndpointMoment3 u t 0)^(2 : ℕ)-(sqbEndpointMoment1 u t 0)^(2 : ℕ)*(sqbEndpointMoment4 u t 0-reserve2 u t)+2*sqbEndpointMoment1 u t 0*sqbEndpointMoment2 u t 0*sqbEndpointMoment3 u t 0-(sqbEndpointMoment2 u t 0)^(2 : ℕ)*(sqbEndpointMoment2 u t 0-reserve1 u t) := by
  simp only [sqbEndpointMoment0, sqbEndpointMoment1, sqbEndpointMoment2,
    sqbEndpointMoment3, sqbEndpointMoment4, reserve0, reserve1, reserve2,
    sqbEndpointA, sqbEndpointB, sqbEndpointU, sqbEndpointV]
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity


private theorem reserved_four_0_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) :
    0 < detSym4
      (sqbEndpointMoment0 u t 0-reserve0 u t)
      (sqbEndpointMoment1 u t 0) (sqbEndpointMoment2 u t 0) (sqbEndpointMoment3 u t 0)
      (sqbEndpointMoment2 u t 0-reserve1 u t)
      (sqbEndpointMoment3 u t 0) (sqbEndpointMoment4 u t 0)
      (sqbEndpointMoment4 u t 0-reserve2 u t)
      (sqbEndpointMoment5 u t 0)
      (sqbEndpointMoment6 u t 0+
        500000000000*sqbEndpointU u t*(sqbEndpointB u t)^(11 : ℕ)*
          (11*sqbEndpointB u t-2*sqbEndpointA u t)*
          (2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)-reserve3 u t) := by
  unfold detSym4 sqbEndpointMoment0 sqbEndpointMoment1 sqbEndpointMoment2
    sqbEndpointMoment3 sqbEndpointMoment4 sqbEndpointMoment5 sqbEndpointMoment6
    reserve0 reserve1 reserve2 reserve3 sqbEndpointA sqbEndpointB sqbEndpointU sqbEndpointV
  dsimp only
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity


private theorem reserved_mass_1_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) : 0 < sqbEndpointMoment0 u t 1-reserve0 u t := by
  simp only [sqbEndpointMoment0, reserve0,
    sqbEndpointA, sqbEndpointB, sqbEndpointU, sqbEndpointV]
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity

private theorem reserved_head_1_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) : 0 < (sqbEndpointMoment0 u t 1-reserve0 u t)*(sqbEndpointMoment2 u t 1-reserve1 u t)-(sqbEndpointMoment1 u t 1)^(2 : ℕ) := by
  simp only [sqbEndpointMoment0, sqbEndpointMoment1, sqbEndpointMoment2,
    reserve0, reserve1,
    sqbEndpointA, sqbEndpointB, sqbEndpointU, sqbEndpointV]
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity

private theorem reserved_three_1_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) : 0 < (sqbEndpointMoment0 u t 1-reserve0 u t)*(sqbEndpointMoment2 u t 1-reserve1 u t)*(sqbEndpointMoment4 u t 1-reserve2 u t)-(sqbEndpointMoment0 u t 1-reserve0 u t)*(sqbEndpointMoment3 u t 1)^(2 : ℕ)-(sqbEndpointMoment1 u t 1)^(2 : ℕ)*(sqbEndpointMoment4 u t 1-reserve2 u t)+2*sqbEndpointMoment1 u t 1*sqbEndpointMoment2 u t 1*sqbEndpointMoment3 u t 1-(sqbEndpointMoment2 u t 1)^(2 : ℕ)*(sqbEndpointMoment2 u t 1-reserve1 u t) := by
  simp only [sqbEndpointMoment0, sqbEndpointMoment1, sqbEndpointMoment2,
    sqbEndpointMoment3, sqbEndpointMoment4, reserve0, reserve1, reserve2,
    sqbEndpointA, sqbEndpointB, sqbEndpointU, sqbEndpointV]
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity


private theorem reserved_four_1_pos {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (hpos : 0 < u+t) :
    0 < detSym4
      (sqbEndpointMoment0 u t 1-reserve0 u t)
      (sqbEndpointMoment1 u t 1) (sqbEndpointMoment2 u t 1) (sqbEndpointMoment3 u t 1)
      (sqbEndpointMoment2 u t 1-reserve1 u t)
      (sqbEndpointMoment3 u t 1) (sqbEndpointMoment4 u t 1)
      (sqbEndpointMoment4 u t 1-reserve2 u t)
      (sqbEndpointMoment5 u t 1)
      (sqbEndpointMoment6 u t 1+
        500000000000*sqbEndpointU u t*(sqbEndpointB u t)^(11 : ℕ)*
          (11*sqbEndpointB u t-2*sqbEndpointA u t)*
          (2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)-reserve3 u t) := by
  unfold detSym4 sqbEndpointMoment0 sqbEndpointMoment1 sqbEndpointMoment2
    sqbEndpointMoment3 sqbEndpointMoment4 sqbEndpointMoment5 sqbEndpointMoment6
    reserve0 reserve1 reserve2 reserve3 sqbEndpointA sqbEndpointB sqbEndpointU sqbEndpointV
  dsimp only
  rcases lt_or_eq_of_le hu with hu | hu
  · ring_nf
    positivity
  · have htpos : 0 < t := by linarith
    subst u
    ring_nf
    positivity


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

private theorem affine_moment0_hom (q r : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment0 (50-10*q) (10*q-37) r =
      (169*twoAtomLowerEnvelope q)*130^(2 : ℕ)*
        twoAtomAffineEvenMoment0 q (r/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment0
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment0
  field_simp [hU]

private theorem affine_moment1_hom (q r : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment1 (50-10*q) (10*q-37) r =
      (169*twoAtomLowerEnvelope q)*130^(4 : ℕ)*
        twoAtomAffineEvenMoment1 q (r/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment1
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment1 twoAtomAffinePart twoAtomOddNumerator1
  field_simp [hU]
  ring

private theorem affine_moment2_hom (q r : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment2 (50-10*q) (10*q-37) r =
      (169*twoAtomLowerEnvelope q)*130^(6 : ℕ)*
        twoAtomAffineEvenMoment2 q (r/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment2
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment2 twoAtomAffinePart twoAtomOddNumerator2
  field_simp [hU]
  ring

private theorem affine_moment3_hom (q r : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment3 (50-10*q) (10*q-37) r =
      (169*twoAtomLowerEnvelope q)*130^(8 : ℕ)*
        twoAtomAffineEvenMoment3 q (r/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment3
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment3 twoAtomAffinePart twoAtomOddNumerator3
  field_simp [hU]
  ring

private theorem affine_moment4_hom (q r : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment4 (50-10*q) (10*q-37) r =
      (169*twoAtomLowerEnvelope q)*130^(10 : ℕ)*
        twoAtomAffineEvenMoment4 q (r/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment4
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment4 twoAtomAffinePart twoAtomOddNumerator4
  field_simp [hU]
  ring


private theorem affine_moment5_hom (q r : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment5 (50-10*q) (10*q-37) r =
      (169*twoAtomLowerEnvelope q)*130^(12 : ℕ)*
        twoAtomAffineEvenMoment5 q (r/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment5
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment5 twoAtomAffinePart twoAtomOddNumerator5
  field_simp [hU]
  ring

private theorem affine_moment6_hom (q r : ℝ) (hU : twoAtomLowerEnvelope q ≠ 0) :
    sqbEndpointMoment6 (50-10*q) (10*q-37) r =
      (169*twoAtomLowerEnvelope q)*130^(14 : ℕ)*
        twoAtomAffineEvenMoment6 q (r/twoAtomLowerEnvelope q) := by
  obtain ⟨hA,hB,hUe,hV⟩ := affine_scale_identities q
  unfold sqbEndpointMoment6
  rw [hA,hB,hUe,hV]
  unfold twoAtomAffineEvenMoment6
  field_simp [hU]

private def symQuadratic (a b c d e f g h i j x y z w : ℝ) : ℝ :=
  a*x^(2 : ℕ)+2*b*x*y+2*c*x*z+2*d*x*w+e*y^(2 : ℕ)+2*f*y*z+2*g*y*w+
    h*z^(2 : ℕ)+2*i*z*w+j*w^(2 : ℕ)

private theorem symQuadratic_nonneg {a b c d e f g h i j : ℝ}
    (ha : 0 < a) (h2 : 0 < a*e-b^(2 : ℕ))
    (h3 : 0 < a*e*h-a*f^(2 : ℕ)-b^(2 : ℕ)*h+2*b*c*f-c^(2 : ℕ)*e)
    (h4 : 0 ≤ detSym4 a b c d e f g h i j) (x y z w : ℝ) :
    0 ≤ symQuadratic a b c d e f g h i j x y z w := by
  let D2 := a*e-b^(2 : ℕ)
  let D3 := a*e*h-a*f^(2 : ℕ)-b^(2 : ℕ)*h+2*b*c*f-c^(2 : ℕ)*e
  let E := a*e*i-a*f*g-b^(2 : ℕ)*i+b*c*g+b*d*f-c*d*e
  have he : a*D2*D3*symQuadratic a b c d e f g h i j x y z w =
      D2*D3*(a*x+b*y+c*z+d*w)^(2 : ℕ) +
      D3*(D2*y+(a*f-b*c)*z+(a*g-b*d)*w)^(2 : ℕ) +
      a*(D3*z+E*w)^(2 : ℕ)+a*D2*detSym4 a b c d e f g h i j*w^(2 : ℕ) := by
    dsimp [D2,D3,E,symQuadratic,detSym4]
    ring
  have hd2 : 0 < D2 := h2
  have hd3 : 0 < D3 := h3
  have hp : 0 ≤ a*D2*D3*symQuadratic a b c d e f g h i j x y z w := by
    rw [he]
    positivity
  exact (mul_nonneg_iff_of_pos_left (mul_pos (mul_pos ha hd2) hd3)).mp hp

/-- The corrected affine energy, with all ten symmetric coefficients retained. -/
def twoAtomAffineEvenFourCorrectedQuadratic (q z x y v w : ℝ) : ℝ :=
  twoAtomAffineEvenMoment0 q z*x^(2 : ℕ)+2*twoAtomAffineEvenMoment1 q z*x*y+
    2*twoAtomAffineEvenMoment2 q z*x*v+2*twoAtomAffineEvenMoment3 q z*x*w+
    twoAtomAffineEvenMoment2 q z*y^(2 : ℕ)+2*twoAtomAffineEvenMoment3 q z*y*v+
    2*twoAtomAffineEvenMoment4 q z*y*w+twoAtomAffineEvenMoment4 q z*v^(2 : ℕ)+
    2*twoAtomAffineEvenMoment5 q z*v*w+
    (twoAtomAffineEvenMoment6 q z+1000000000000*(11/2-q)*(2*q-3)^(2 : ℕ))*w^(2 : ℕ)

/-- Coordinate-specific positive reserves available for the complete sixteen-entry tail. -/
def twoAtomAffineEvenFourDiagonalReserve (q x y v w : ℝ) : ℝ :=
  (2*q-3)^(2 : ℕ)*(x^(2 : ℕ)/1000000+(8*q)^(2 : ℕ)*y^(2 : ℕ)/10000+(8*q)^(4 : ℕ)*v^(2 : ℕ)/10+
    (500*(5-q)^(2 : ℕ)+1)*(8*q)^(6 : ℕ)*w^(2 : ℕ))

private theorem reserved_endpoint_quadratic {q r : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hr : r = 0 ∨ r = 1) (x y v w : ℝ) :
    twoAtomAffineEvenFourDiagonalReserve q x y v w ≤
      twoAtomAffineEvenFourCorrectedQuadratic q (r/twoAtomLowerEnvelope q) x y v w := by
  have hU := affine_envelope_pos hq
  let u := 50-10*q
  let t := 10*q-37
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hup : 0 < u+t := by dsimp [u,t]; linarith
  have hmass : 0 < sqbEndpointMoment0 u t r-reserve0 u t := by
    rcases hr with rfl | rfl
    · exact reserved_mass_0_pos hu ht hup
    · exact reserved_mass_1_pos hu ht hup
  have hhead : 0 < (sqbEndpointMoment0 u t r-reserve0 u t)*
      (sqbEndpointMoment2 u t r-reserve1 u t)-(sqbEndpointMoment1 u t r)^(2 : ℕ) := by
    rcases hr with rfl | rfl
    · exact reserved_head_0_pos hu ht hup
    · exact reserved_head_1_pos hu ht hup
  have hthree : 0 < (sqbEndpointMoment0 u t r-reserve0 u t)*
      (sqbEndpointMoment2 u t r-reserve1 u t)*(sqbEndpointMoment4 u t r-reserve2 u t)-
      (sqbEndpointMoment0 u t r-reserve0 u t)*(sqbEndpointMoment3 u t r)^(2 : ℕ)-
      (sqbEndpointMoment1 u t r)^(2 : ℕ)*(sqbEndpointMoment4 u t r-reserve2 u t)+
      2*sqbEndpointMoment1 u t r*sqbEndpointMoment2 u t r*sqbEndpointMoment3 u t r-
      (sqbEndpointMoment2 u t r)^(2 : ℕ)*(sqbEndpointMoment2 u t r-reserve1 u t) := by
    rcases hr with rfl | rfl
    · exact reserved_three_0_pos hu ht hup
    · exact reserved_three_1_pos hu ht hup
  have hfour : 0 ≤ detSym4
      (sqbEndpointMoment0 u t r-reserve0 u t)
      (sqbEndpointMoment1 u t r) (sqbEndpointMoment2 u t r) (sqbEndpointMoment3 u t r)
      (sqbEndpointMoment2 u t r-reserve1 u t)
      (sqbEndpointMoment3 u t r) (sqbEndpointMoment4 u t r)
      (sqbEndpointMoment4 u t r-reserve2 u t) (sqbEndpointMoment5 u t r)
      (sqbEndpointMoment6 u t r+
        500000000000*sqbEndpointU u t*(sqbEndpointB u t)^(11 : ℕ)*
          (11*sqbEndpointB u t-2*sqbEndpointA u t)*
          (2*sqbEndpointA u t-3*sqbEndpointB u t)^(2 : ℕ)-reserve3 u t) := by
    rcases hr with rfl | rfl
    · exact (reserved_four_0_pos hu ht hup).le
    · exact (reserved_four_1_pos hu ht hup).le
  have h := symQuadratic_nonneg hmass hhead hthree hfour (130^(6 : ℕ)*x) (130^(4 : ℕ)*y) (130^(2 : ℕ)*v) w
  dsimp only [u,t] at h
  rw [affine_moment0_hom q r hU.ne',affine_moment1_hom q r hU.ne',
    affine_moment2_hom q r hU.ne',affine_moment3_hom q r hU.ne',
    affine_moment4_hom q r hU.ne',affine_moment5_hom q r hU.ne',
    affine_moment6_hom q r hU.ne'] at h
  unfold reserve0 reserve1 reserve2 reserve3 at h
  rw [(affine_scale_identities q).1,(affine_scale_identities q).2.1,
    (affine_scale_identities q).2.2.1] at h
  have he : 0 ≤ (169*twoAtomLowerEnvelope q)*130^(14 : ℕ)*
      (twoAtomAffineEvenFourCorrectedQuadratic q (r/twoAtomLowerEnvelope q) x y v w-
        twoAtomAffineEvenFourDiagonalReserve q x y v w) := by
    convert h using 1
    unfold symQuadratic twoAtomAffineEvenFourCorrectedQuadratic twoAtomAffineEvenFourDiagonalReserve
    ring
  have hp := (mul_nonneg_iff_of_pos_left (by positivity)).mp he
  linarith only [hp]

/-- A positive diagonal reserve survives across the whole admitted affine weight interval. -/
theorem twoAtomAffineEvenFourDiagonalReserve_le {q z : ℝ}
    (hq : 37/10 ≤ q) (hqu : q ≤ 5) (hz : 0 ≤ z)
    (hzU : twoAtomLowerEnvelope q*z ≤ 1) (x y v w : ℝ) :
    twoAtomAffineEvenFourDiagonalReserve q x y v w ≤
      twoAtomAffineEvenFourCorrectedQuadratic q z x y v w := by
  have hU := affine_envelope_pos hq
  have hzero := reserved_endpoint_quadratic (r:=0) hq hqu (Or.inl rfl) x y v w
  have hone := reserved_endpoint_quadratic (r:=1) hq hqu (Or.inr rfl) x y v w
  simp only [zero_div] at hzero
  have h0 := mul_le_mul_of_nonneg_left hzero (show 0 ≤ 1-twoAtomLowerEnvelope q*z by linarith)
  have h1 := mul_le_mul_of_nonneg_left hone (mul_nonneg hU.le hz)
  have he : twoAtomAffineEvenFourCorrectedQuadratic q z x y v w =
      (1-twoAtomLowerEnvelope q*z)*twoAtomAffineEvenFourCorrectedQuadratic q 0 x y v w+
      (twoAtomLowerEnvelope q*z)*twoAtomAffineEvenFourCorrectedQuadratic q (1/twoAtomLowerEnvelope q) x y v w := by
    unfold twoAtomAffineEvenFourCorrectedQuadratic twoAtomAffineEvenMoment0
      twoAtomAffineEvenMoment1 twoAtomAffineEvenMoment2 twoAtomAffineEvenMoment3
      twoAtomAffineEvenMoment4 twoAtomAffineEvenMoment5 twoAtomAffineEvenMoment6
      twoAtomAffinePart twoAtomOddNumerator1 twoAtomOddNumerator2 twoAtomOddNumerator3
      twoAtomOddNumerator4 twoAtomOddNumerator5
    field_simp [hU.ne']
    ring
  rw [he]
  nlinarith only [h0,h1]

end
end HTGeometry
