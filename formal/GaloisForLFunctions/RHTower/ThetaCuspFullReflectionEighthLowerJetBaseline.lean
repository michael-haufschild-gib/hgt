import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthLikelihoodGain
import GaloisForLFunctions.RHTower.ThetaCuspReflectedEighthPolynomial

/-!
# Strict eighth baseline after the lower likelihood perturbations

The exact first theta atom remains strictly rank-three positive after the full second- and
fourth-log-jet likelihood losses are inserted, provided only the sixth likelihood loss is held
back.  Two global profile certificates control the relevant curvature and fourth-jet
monotonicities from the physical support edge `q = 41/25`.

Consequently, the unresolved complete-source eighth sign is not a lower-jet stability problem:
it is exactly the coupled sixth/eighth likelihood displacement.
-/

namespace RHTower

noncomputable section

/-- Exact first-atom eighth log-jet profile in Born--Witten weight coordinates. -/
def thetaCuspFirstAtomEighthProfile (q : ℝ) : ℝ :=
  (2 * q + 3) *
    (128 + 192 / q ^ (2 : ℕ) + 36288 / q ^ (3 : ℕ) + 780192 / q ^ (4 : ℕ) +
      5443200 / q ^ (5 : ℕ) + 16329600 / q ^ (6 : ℕ) + 22044960 / q ^ (7 : ℕ) +
      11022480 / q ^ (8 : ℕ))

/-- Exact first-atom baseline at the worst second-jet loss, before any sixth-jet loss. -/
def thetaCuspFirstAtomEighthNoSixthLossBaseline (q : ℝ) : ℝ :=
  thetaCuspReflectedEighthPolynomial
    (thetaCuspFirstAtomCurvatureProfile q - 13 / 10)
    (thetaCuspFirstAtomFourthProfile q)
    (thetaCuspFirstAtomSixthProfile q)
    (thetaCuspFirstAtomEighthProfile q)

/-- The exact no-sixth-loss baseline is strictly positive from the physical support edge. -/
theorem thetaCuspFirstAtomEighthNoSixthLossBaseline_pos
    {q : ℝ} (hq : (41 / 25 : ℝ) ≤ q) :
    0 < thetaCuspFirstAtomEighthNoSixthLossBaseline q := by
  have hqpos : 0 < q := by linarith
  let y := q - 41 / 25
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) * thetaCuspFirstAtomEighthNoSixthLossBaseline q := by
    dsimp [thetaCuspFirstAtomEighthNoSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial, thetaCuspFirstAtomCurvatureProfile,
      thetaCuspFirstAtomFourthProfile, thetaCuspFirstAtomSixthProfile,
      thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 41 / 25 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The curvature derivative bracket is positive at the worst admissible curvature. -/
theorem thetaCuspFirstAtomEighthCurvatureDerivativeBracket_pos
    {q : ℝ} (hq : (41 / 25 : ℝ) ≤ q) :
    let Aw := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let C0 := thetaCuspFirstAtomSixthProfile q
    let D0 := thetaCuspFirstAtomEighthProfile q
    0 < 576 * Aw ^ (4 : ℕ) - 672 * Aw ^ (2 : ℕ) * B0 + 76 * B0 ^ (2 : ℕ) +
      48 * Aw * C0 - D0 := by
  have hqpos : 0 < q := by linarith
  let y := q - 41 / 25
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ (16 : ℕ) *
      (576 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (4 : ℕ) -
        672 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) *
          thetaCuspFirstAtomFourthProfile q +
        76 * thetaCuspFirstAtomFourthProfile q ^ (2 : ℕ) +
        48 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          thetaCuspFirstAtomSixthProfile q -
        thetaCuspFirstAtomEighthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 41 / 25 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The fourth-jet displacement constant is positive at the worst admissible curvature. -/
theorem thetaCuspFirstAtomEighthFourthDisplacementConstant_pos
    {q : ℝ} (hq : (41 / 25 : ℝ) ≤ q) :
    let Aw := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let D0 := thetaCuspFirstAtomEighthProfile q
    0 < 1344 * Aw ^ (4 : ℕ) - 608 * Aw ^ (2 : ℕ) * B0 + 204 * B0 ^ (2 : ℕ) - D0 := by
  have hqpos : 0 < q := by linarith
  let y := q - 41 / 25
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ (16 : ℕ) *
      (1344 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (4 : ℕ) -
        608 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) *
          thetaCuspFirstAtomFourthProfile q +
        204 * thetaCuspFirstAtomFourthProfile q ^ (2 : ℕ) -
        thetaCuspFirstAtomEighthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 41 / 25 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The exact linear coefficient of the sixth likelihood loss is already positive at the worst
admissible curvature. -/
theorem thetaCuspFirstAtomEighthSixthLossCoefficient_pos
    {q : ℝ} (hq : (41 / 25 : ℝ) ≤ q) :
    0 < 128 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (3 : ℕ) -
      2 * thetaCuspFirstAtomSixthProfile q := by
  have hqpos : 0 < q := by linarith
  let y := q - 41 / 25
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (6 : ℕ) *
      (128 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (3 : ℕ) -
        2 * thetaCuspFirstAtomSixthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 41 / 25 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 6]

/-- Under the sharp profile ratio, raising curvature cannot decrease the eighth polynomial. -/
theorem thetaCuspReflectedEighthPolynomial_mono_curvature
    {Aw A B C D : ℝ} (hAwpos : 0 < Aw) (hAwA : Aw ≤ A)
    (hB : B < (7 / 5 : ℝ) * Aw ^ (2 : ℕ)) (hC : 0 < C)
    (hG : 0 < 576 * Aw ^ (4 : ℕ) - 672 * Aw ^ (2 : ℕ) * B + 76 * B ^ (2 : ℕ) +
      48 * Aw * C - D) :
    thetaCuspReflectedEighthPolynomial Aw B C D ≤
      thetaCuspReflectedEighthPolynomial A B C D := by
  let G : ℝ → ℝ := fun t =>
    576 * t ^ (4 : ℕ) - 672 * t ^ (2 : ℕ) * B + 76 * B ^ (2 : ℕ) + 48 * t * C - D
  let f : ℝ → ℝ := fun t => thetaCuspReflectedEighthPolynomial t B C D
  have hGpos : ∀ t, Aw ≤ t → 0 < G t := by
    intro t ht
    have htpos : 0 < t := hAwpos.trans_le ht
    have htsq : Aw ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := pow_le_pow_left₀ hAwpos.le ht 2
    have hcore : 0 < 576 * (t ^ (2 : ℕ) + Aw ^ (2 : ℕ)) - 672 * B := by
      nlinarith
    have hfactor : 0 <
        (t + Aw) * (576 * (t ^ (2 : ℕ) + Aw ^ (2 : ℕ)) - 672 * B) + 48 * C := by
      positivity
    have hdiff : G t - G Aw =
        (t - Aw) *
          ((t + Aw) * (576 * (t ^ (2 : ℕ) + Aw ^ (2 : ℕ)) - 672 * B) + 48 * C) := by
      dsimp only [G]
      ring
    have hGAw : 0 < G Aw := by simpa only [G] using hG
    rw [hdiff] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hfactor.le]
  have hf' : ∀ t : ℝ, HasDerivAt f (8 * t * G t) t := by
    intro t
    dsimp only [f, G, thetaCuspReflectedEighthPolynomial]
    convert (((((((((hasDerivAt_id t).pow 6).const_mul 768).sub
        (((hasDerivAt_id t).pow 4).mul_const B |>.const_mul 1344)).add
        (((hasDerivAt_id t).pow 2).mul_const (B ^ (2 : ℕ)) |>.const_mul 304)).sub
        (hasDerivAt_const t (68 * B ^ (3 : ℕ)))).add
        (((hasDerivAt_id t).pow 3).mul_const C |>.const_mul 128)).sub
        (((hasDerivAt_id t).pow 2).mul_const D |>.const_mul 4)).add
        (hasDerivAt_const t (B * D))).sub
        (hasDerivAt_const t (C ^ (2 : ℕ))) using 1
    all_goals try rfl
    · funext y
      simp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, id_eq]
      ring
    · norm_num
      ring
  have hstrict : StrictMonoOn f (Set.Ici Aw) :=
    strictMonoOn_of_deriv_pos (convex_Ici Aw) (by
      dsimp only [f, thetaCuspReflectedEighthPolynomial]
      fun_prop) (by
      intro t ht
      rw [interior_Ici] at ht
      have hAwt : Aw < t := by simpa using ht
      rw [(hf' t).deriv]
      exact mul_pos (mul_pos (by norm_num) (hAwpos.trans hAwt))
        (hGpos t hAwt.le))
  exact hstrict.monotoneOn (by simp) (by simpa using hAwA) hAwA

/-- Under the same ratio, a strict downward fourth-jet displacement raises the polynomial. -/
theorem thetaCuspReflectedEighthPolynomial_strictAnti_fourth
    {Aw A B B0 C D : ℝ} (hAwpos : 0 < Aw) (hAwA : Aw ≤ A)
    (hBB0 : B < B0) (hB0 : B0 < (7 / 5 : ℝ) * Aw ^ (2 : ℕ))
    (hK : 0 < 1344 * Aw ^ (4 : ℕ) - 608 * Aw ^ (2 : ℕ) * B0 + 204 * B0 ^ (2 : ℕ) - D) :
    thetaCuspReflectedEighthPolynomial A B0 C D <
      thetaCuspReflectedEighthPolynomial A B C D := by
  let e := B0 - B
  let K : ℝ → ℝ := fun t =>
    1344 * t ^ (4 : ℕ) - 608 * t ^ (2 : ℕ) * B0 + 204 * B0 ^ (2 : ℕ) - D
  have he : 0 < e := by dsimp only [e]; linarith
  have hAsq : Aw ^ (2 : ℕ) ≤ A ^ (2 : ℕ) := pow_le_pow_left₀ hAwpos.le hAwA 2
  have hlinear : 0 < 304 * A ^ (2 : ℕ) - 204 * B0 := by nlinarith
  have hcore : 0 < 1344 * (A ^ (2 : ℕ) + Aw ^ (2 : ℕ)) - 608 * B0 := by
    nlinarith
  have hApos : 0 < A := hAwpos.trans_le hAwA
  have hfactor : 0 ≤
      (A - Aw) * (A + Aw) *
        (1344 * (A ^ (2 : ℕ) + Aw ^ (2 : ℕ)) - 608 * B0) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hAwA) (add_pos hApos hAwpos).le) hcore.le
  have hKdiff : K A - K Aw =
      (A - Aw) * (A + Aw) *
        (1344 * (A ^ (2 : ℕ) + Aw ^ (2 : ℕ)) - 608 * B0) := by
    dsimp only [K]
    ring
  have hKAw : 0 < K Aw := by simpa only [K] using hK
  have hKA : 0 < K A := by rw [hKdiff] at *; linarith
  have hdiff :
      thetaCuspReflectedEighthPolynomial A B C D -
          thetaCuspReflectedEighthPolynomial A B0 C D =
        e * (68 * e ^ (2 : ℕ) + (304 * A ^ (2 : ℕ) - 204 * B0) * e + K A) := by
    dsimp only [e, K, thetaCuspReflectedEighthPolynomial]
    ring
  rw [← sub_pos, hdiff]
  positivity

/-- Eighth reflected polynomial after exact second/fourth likelihood losses but before the
sixth likelihood loss is inserted. -/
def thetaCuspFullReflectionEighthNoSixthLikelihoodBaseline (x : ℝ) : ℝ :=
  thetaCuspReflectedEighthPolynomial
    (thetaCuspFullReflectedLogCurvature x)
    (thetaCuspFullReflectedLogFourthJet x)
    (thetaCuspBornWittenLogSixthDerivative 1 x)
    (thetaCuspBornWittenLogEighthDerivative 1 x)

/-- Full second/fourth likelihood perturbations preserve a strict eighth baseline globally. -/
theorem thetaCuspFullReflectionEighthNoSixthLikelihoodBaseline_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspFullReflectionEighthNoSixthLikelihoodBaseline x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
  let C0 := thetaCuspBornWittenLogSixthDerivative 1 x
  let D0 := thetaCuspBornWittenLogEighthDerivative 1 x
  let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let A := A0 - e2
  let B := B0 - e4
  let Aw := A0 - 13 / 10
  have hq : (41 / 25 : ℝ) ≤ q := by
    have hpi := Real.pi_gt_d2
    norm_num at hpi
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx
    have he2 : 1 ≤ Real.exp x ^ (2 : ℕ) := by nlinarith [Real.exp_pos x]
    have hscale : Real.pi ≤ thetaCuspMorseScale 1 x := by
      rw [thetaCuspMorseScale]
      norm_num
      simpa using mul_le_mul_of_nonneg_left he2 Real.pi_pos.le
    dsimp only [q]
    rw [thetaCuspBornWittenWeight_eq]
    linarith
  have hqpos : 0 < q := by linarith
  have hA0profile : A0 = thetaCuspFirstAtomCurvatureProfile q := by
    dsimp only [A0, q]
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    rfl
  have hB0profile : B0 = thetaCuspFirstAtomFourthProfile q := by
    dsimp only [B0, q]
    rfl
  have hC0profile : C0 = thetaCuspFirstAtomSixthProfile q := by
    change
      (2 * q + 3) * (32 + 48 / q ^ (2 : ℕ) + 2160 / q ^ (3 : ℕ) +
        16200 / q ^ (4 : ℕ) + 38880 / q ^ (5 : ℕ) + 29160 / q ^ (6 : ℕ)) =
        thetaCuspFirstAtomSixthProfile q
    dsimp only [thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    ring
  have hD0profile : D0 = thetaCuspFirstAtomEighthProfile q := by
    dsimp only [D0, q, thetaCuspBornWittenLogEighthDerivative,
      thetaCuspFirstAtomEighthProfile]
  have hA0 : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using
      nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx
  have hC0 : 0 < C0 := by
    simpa only [C0] using
      thetaCuspBornWittenLogSixthDerivative_pos (n := 1) (by norm_num) hx
  have hB0upper : B0 ≤ (6 / 5 : ℝ) * A0 ^ (2 : ℕ) := by
    simpa only [A0, B0] using
      thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq
        (n := 1) (by norm_num) hx
  have he2upper : e2 ≤ (13 / 10 : ℝ) := by
    simpa only [e2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  have he4pos : 0 < e4 := by
    simpa only [e4] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx
  have hAwpos : 0 < Aw := by dsimp only [Aw]; linarith
  have hAwA : Aw ≤ A := by dsimp only [Aw, A]; linarith
  have hBB0 : B < B0 := by dsimp only [B]; linarith
  have hAwRatio : (177 / 190 : ℝ) * A0 ≤ Aw := by
    dsimp only [Aw]
    nlinarith
  have hratioSq : (177 / 190 : ℝ) ^ (2 : ℕ) * A0 ^ (2 : ℕ) ≤ Aw ^ (2 : ℕ) := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (177 / 190) * A0)
      hAwRatio 2
    simpa only [mul_pow] using hpow
  have hB0Aw : B0 < (7 / 5 : ℝ) * Aw ^ (2 : ℕ) := by
    have hcoef : (6 / 5 : ℝ) < (7 / 5 : ℝ) * (177 / 190) ^ (2 : ℕ) := by norm_num
    have hA0sq : 0 < A0 ^ (2 : ℕ) := by positivity
    have hstrict : (6 / 5 : ℝ) * A0 ^ (2 : ℕ) <
        ((7 / 5 : ℝ) * (177 / 190) ^ (2 : ℕ)) * A0 ^ (2 : ℕ) :=
      mul_lt_mul_of_pos_right hcoef hA0sq
    nlinarith
  have hbase : 0 < thetaCuspReflectedEighthPolynomial Aw B0 C0 D0 := by
    dsimp only [Aw]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only [thetaCuspFirstAtomEighthNoSixthLossBaseline] using
      thetaCuspFirstAtomEighthNoSixthLossBaseline_pos hq
  have hG : 0 < 576 * Aw ^ (4 : ℕ) - 672 * Aw ^ (2 : ℕ) * B0 + 76 * B0 ^ (2 : ℕ) +
      48 * Aw * C0 - D0 := by
    dsimp only [Aw]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only using thetaCuspFirstAtomEighthCurvatureDerivativeBracket_pos hq
  have hK : 0 < 1344 * Aw ^ (4 : ℕ) - 608 * Aw ^ (2 : ℕ) * B0 + 204 * B0 ^ (2 : ℕ) - D0 := by
    dsimp only [Aw]
    rw [hA0profile, hB0profile, hD0profile]
    simpa only using thetaCuspFirstAtomEighthFourthDisplacementConstant_pos hq
  have hAmono : thetaCuspReflectedEighthPolynomial Aw B0 C0 D0 ≤
      thetaCuspReflectedEighthPolynomial A B0 C0 D0 :=
    thetaCuspReflectedEighthPolynomial_mono_curvature hAwpos hAwA hB0Aw hC0 hG
  have hBmono : thetaCuspReflectedEighthPolynomial A B0 C0 D0 <
      thetaCuspReflectedEighthPolynomial A B C0 D0 :=
    thetaCuspReflectedEighthPolynomial_strictAnti_fourth hAwpos hAwA hBB0 hB0Aw hK
  change 0 < thetaCuspReflectedEighthPolynomial A B C0 D0
  exact hbase.trans_le hAmono |>.trans hBmono

/-- Exact loss caused by inserting the positive literal sixth likelihood jet into the otherwise
strict no-sixth-loss baseline. -/
def thetaCuspFullReflectionEighthSixthLikelihoodLoss (x : ℝ) : ℝ :=
  let A := thetaCuspFullReflectedLogCurvature x
  let C0 := thetaCuspBornWittenLogSixthDerivative 1 x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  (128 * A ^ (3 : ℕ) - 2 * C0) * e6 + e6 ^ (2 : ℕ)

/-- Exact net likelihood margin: favorable eighth gain minus unfavorable sixth displacement. -/
def thetaCuspFullReflectionEighthCoupledLikelihoodMargin (x : ℝ) : ℝ :=
  let A := thetaCuspFullReflectedLogCurvature x
  let B := thetaCuspFullReflectedLogFourthJet x
  let e8 := thetaCuspLikelihoodSourceLogPartitionJetEight x
  (4 * A ^ (2 : ℕ) - B) * e8 - thetaCuspFullReflectionEighthSixthLikelihoodLoss x

/-- The sixth likelihood loss has a strictly positive linear coefficient throughout the
positive source half-line. -/
theorem thetaCuspFullReflectionEighthSixthLossCoefficient_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < 128 * thetaCuspFullReflectedLogCurvature x ^ (3 : ℕ) -
      2 * thetaCuspBornWittenLogSixthDerivative 1 x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let C0 := thetaCuspBornWittenLogSixthDerivative 1 x
  let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let A := A0 - e2
  let Aw := A0 - 13 / 10
  have hq : (41 / 25 : ℝ) ≤ q := by
    have hpi := Real.pi_gt_d2
    norm_num at hpi
    have he : 1 ≤ Real.exp x := Real.one_le_exp hx
    have he2 : 1 ≤ Real.exp x ^ (2 : ℕ) := by nlinarith [Real.exp_pos x]
    have hscale : Real.pi ≤ thetaCuspMorseScale 1 x := by
      rw [thetaCuspMorseScale]
      norm_num
      simpa using mul_le_mul_of_nonneg_left he2 Real.pi_pos.le
    dsimp only [q]
    rw [thetaCuspBornWittenWeight_eq]
    linarith
  have hqpos : 0 < q := by linarith
  have hA0profile : A0 = thetaCuspFirstAtomCurvatureProfile q := by
    dsimp only [A0, q]
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    rfl
  have hC0profile : C0 = thetaCuspFirstAtomSixthProfile q := by
    change
      (2 * q + 3) * (32 + 48 / q ^ (2 : ℕ) + 2160 / q ^ (3 : ℕ) +
        16200 / q ^ (4 : ℕ) + 38880 / q ^ (5 : ℕ) + 29160 / q ^ (6 : ℕ)) =
        thetaCuspFirstAtomSixthProfile q
    dsimp only [thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    ring
  have hA0 : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using
      nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx
  have he2upper : e2 ≤ (13 / 10 : ℝ) := by
    simpa only [e2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  have hAwpos : 0 < Aw := by dsimp only [Aw]; linarith
  have hAwA : Aw ≤ A := by dsimp only [Aw, A]; linarith
  have hcube : Aw ^ (3 : ℕ) ≤ A ^ (3 : ℕ) := pow_le_pow_left₀ hAwpos.le hAwA 3
  have hworst : 0 < 128 * Aw ^ (3 : ℕ) - 2 * C0 := by
    dsimp only [Aw]
    rw [hA0profile, hC0profile]
    exact thetaCuspFirstAtomEighthSixthLossCoefficient_pos hq
  change 0 < 128 * A ^ (3 : ℕ) - 2 * C0
  nlinarith

/-- The literal sixth likelihood perturbation creates a strictly positive rank-three loss. -/
theorem thetaCuspFullReflectionEighthSixthLikelihoodLoss_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspFullReflectionEighthSixthLikelihoodLoss x := by
  have hcoef := thetaCuspFullReflectionEighthSixthLossCoefficient_pos hx
  have he6 := thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx
  unfold thetaCuspFullReflectionEighthSixthLikelihoodLoss
  exact add_pos_of_pos_of_nonneg (mul_pos hcoef he6) (sq_nonneg _)

/-- The Born-top baseline is exactly the strict lower-jet baseline minus the sixth likelihood
loss; no estimate is used. -/
theorem thetaCuspFullReflectionEighthBornTopBaseline_eq_noSixthBaseline_sub_sixthLoss
    (x : ℝ) :
    thetaCuspFullReflectionEighthBornTopBaseline x =
      thetaCuspFullReflectionEighthNoSixthLikelihoodBaseline x -
        thetaCuspFullReflectionEighthSixthLikelihoodLoss x := by
  unfold thetaCuspFullReflectionEighthBornTopBaseline
    thetaCuspFullReflectionEighthNoSixthLikelihoodBaseline
    thetaCuspFullReflectionEighthSixthLikelihoodLoss
    thetaCuspReflectedEighthPolynomial thetaCuspFullReflectedLogSixthJet
  ring

/-- Exact final D1 decomposition: strict lower-jet baseline plus one coupled sixth/eighth
likelihood margin. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_eq_noSixthBaseline_add_coupledMargin
    (x : ℝ) :
    thetaCuspFullReflectionEighthHankelCurvature x =
      thetaCuspFullReflectionEighthNoSixthLikelihoodBaseline x +
        thetaCuspFullReflectionEighthCoupledLikelihoodMargin x := by
  rw [thetaCuspFullReflectionEighthHankelCurvature_eq_baseline_add_likelihoodGain,
    thetaCuspFullReflectionEighthBornTopBaseline_eq_noSixthBaseline_sub_sixthLoss]
  unfold thetaCuspFullReflectionEighthCoupledLikelihoodMargin
  ring

/-- Unconditional exact characterization of the sole remaining positive-half-line D1 burden. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_iff_coupledLikelihoodAbsorption
    (x : ℝ) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x ↔
      thetaCuspFullReflectionEighthSixthLikelihoodLoss x <
        thetaCuspFullReflectionEighthNoSixthLikelihoodBaseline x +
          (4 * thetaCuspFullReflectedLogCurvature x ^ (2 : ℕ) -
            thetaCuspFullReflectedLogFourthJet x) *
              thetaCuspLikelihoodSourceLogPartitionJetEight x := by
  rw [thetaCuspFullReflectionEighthHankelCurvature_eq_noSixthBaseline_add_coupledMargin]
  unfold thetaCuspFullReflectionEighthCoupledLikelihoodMargin
  constructor <;> intro h <;> linarith

end

end RHTower
