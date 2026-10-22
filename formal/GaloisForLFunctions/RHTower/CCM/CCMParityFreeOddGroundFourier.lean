import GaloisForLFunctions.RHTower.CCM.CCMSourceResponseDeterminantDichotomy

/-!
# Parity-free simple-ground CCM Fourier law

Formalizes the odd half of the finite simple-ground theorem left open by the even-ground argument
of Connes--van Suijlekom.  Exact rank-two cross-commutator data force a positive coupling constant.
A source completion of squared frequency is then self-adjoint and nonnegative in the degenerate
CCM metric.  Its determinant identity implies that every non-pole zero of the odd Fourier
resolvent numerator is real.  No spectral conclusion is stored in the input structure.
-/

open Matrix Complex
open scoped ComplexOrder MatrixOrder

namespace RHTower

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem norm_star_dotProduct_sq_le (x y : n → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤
      (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re := by
  let X : EuclideanSpace ℂ n := WithLp.toLp 2 x
  let Y : EuclideanSpace ℂ n := WithLp.toLp 2 y
  have h := inner_mul_inner_self_le (𝕜 := ℂ) X Y
  have hXY : inner ℂ X Y = star x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [X, Y, dotProduct, mul_comm]
  have hYX : inner ℂ Y X = star y ⬝ᵥ x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [X, Y, dotProduct, mul_comm]
  have hXX : inner ℂ X X = star x ⬝ᵥ x := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [X, dotProduct, mul_comm]
  have hYY : inner ℂ Y Y = star y ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Y, dotProduct, mul_comm]
  rw [hXY, hYX, hXX, hYY] at h
  have hnorm : ‖star y ⬝ᵥ x‖ = ‖star x ⬝ᵥ y‖ := by
    have heq : star y ⬝ᵥ x = star (star x ⬝ᵥ y) := by
      rw [Matrix.star_dotProduct]
    rw [heq, norm_star]
  rw [hnorm, ← pow_two] at h
  exact h

theorem norm_semimetric_pairing_sq_le
    (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) (x y : n → ℂ) :
    ‖star x ⬝ᵥ (Q *ᵥ y)‖ ^ 2 ≤
      (star x ⬝ᵥ (Q *ᵥ x)).re * (star y ⬝ᵥ (Q *ᵥ y)).re := by
  let V : Matrix n n ℂ := CFC.sqrt Q
  have hVpsd : V.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hfac : Q = V * Vᴴ := by
    rw [hVpsd.isHermitian, ← sq, CFC.sq_sqrt Q]
  have hpair_general (u v : n → ℂ) :
      star (Vᴴ *ᵥ u) ⬝ᵥ (Vᴴ *ᵥ v) = star u ⬝ᵥ (Q *ᵥ v) := by
    rw [show star (Vᴴ *ᵥ u) = star u ᵥ* V by
      simp [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← hfac]
  let X : n → ℂ := Vᴴ *ᵥ x
  let Y : n → ℂ := Vᴴ *ᵥ y
  have hpair : star X ⬝ᵥ Y = star x ⬝ᵥ (Q *ᵥ y) := by
    simpa [X, Y] using hpair_general x y
  have hxx : star X ⬝ᵥ X = star x ⬝ᵥ (Q *ᵥ x) := by
    simpa [X] using hpair_general x x
  have hyy : star Y ⬝ᵥ Y = star y ⬝ᵥ (Q *ᵥ y) := by
    simpa [Y] using hpair_general y y
  have h := norm_star_dotProduct_sq_le X Y
  rw [hpair, hxx, hyy] at h
  exact h

/-- Exact block data of a simple odd CCM ground.  The cross relation is the odd-to-even block of
the rank-two frequency commutator; no spectral conclusion is stored in the data. -/
structure CCMParityFreeOddGroundData
    (even odd : Type*) [Fintype even] [Fintype odd]
    [DecidableEq even] [DecidableEq odd] where
  Qplus : Matrix even even ℂ
  Qminus : Matrix odd odd ℂ
  frequency : Matrix even odd ℂ
  eta : even → ℂ
  beta : odd → ℂ
  ground : odd → ℂ
  plus_posSemidef : Qplus.PosSemidef
  minus_posSemidef : Qminus.PosSemidef
  cross_commutator :
    Qplus * frequency - frequency * Qminus = Matrix.vecMulVec eta (star beta)
  ground_kernel : Qminus *ᵥ ground = 0
  ground_radical : ∀ v : odd → ℂ, Qminus *ᵥ v = 0 → ∃ a : ℂ, v = a • ground
  frequency_ground_not_kernel : Qplus *ᵥ (frequency *ᵥ ground) ≠ 0
  normalized : star ground ⬝ᵥ (frequencyᴴ *ᵥ eta) = 1

namespace CCMParityFreeOddGroundData

variable {even odd : Type*} [Fintype even] [Fintype odd]
  [DecidableEq even] [DecidableEq odd]

def delta (S : CCMParityFreeOddGroundData even odd) : odd → ℂ :=
  S.frequencyᴴ *ᵥ S.eta

def squaredFrequency (S : CCMParityFreeOddGroundData even odd) : Matrix odd odd ℂ :=
  S.frequencyᴴ * S.frequency

def betaGround (S : CCMParityFreeOddGroundData even odd) : ℂ :=
  star S.beta ⬝ᵥ S.ground

def completion (S : CCMParityFreeOddGroundData even odd) : Matrix odd odd ℂ :=
  ccmSourceCompletion S.squaredFrequency S.ground S.delta

theorem frequency_ground_ne_zero (S : CCMParityFreeOddGroundData even odd) :
    S.frequency *ᵥ S.ground ≠ 0 := by
  intro hzero
  have hpair : star S.ground ⬝ᵥ (S.frequencyᴴ *ᵥ S.eta) =
      star (S.frequency *ᵥ S.ground) ⬝ᵥ S.eta := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  rw [S.normalized, hzero] at hpair
  simp at hpair

theorem qplus_mulVec_frequency_ground (S : CCMParityFreeOddGroundData even odd) :
    S.Qplus *ᵥ (S.frequency *ᵥ S.ground) = S.betaGround • S.eta := by
  have h := congrArg (fun M : Matrix even odd ℂ => M *ᵥ S.ground)
    S.cross_commutator
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    S.ground_kernel, Matrix.mulVec_zero, sub_zero, Matrix.vecMulVec_mulVec] at h
  simpa [betaGround] using h

theorem star_frequency_ground_dot_eta (S : CCMParityFreeOddGroundData even odd) :
    star (S.frequency *ᵥ S.ground) ⬝ᵥ S.eta = 1 := by
  rw [← S.normalized]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

theorem betaGround_pos (S : CCMParityFreeOddGroundData even odd) :
    0 < S.betaGround := by
  have hnonneg := S.plus_posSemidef.dotProduct_mulVec_nonneg
    (S.frequency *ᵥ S.ground)
  have hne : star (S.frequency *ᵥ S.ground) ⬝ᵥ
      (S.Qplus *ᵥ (S.frequency *ᵥ S.ground)) ≠ 0 := by
    intro hzero
    exact S.frequency_ground_not_kernel
      ((S.plus_posSemidef.dotProduct_mulVec_zero_iff
        (S.frequency *ᵥ S.ground)).mp hzero)
  have hpos : 0 < star (S.frequency *ᵥ S.ground) ⬝ᵥ
      (S.Qplus *ᵥ (S.frequency *ᵥ S.ground)) :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  rw [S.qplus_mulVec_frequency_ground, dotProduct_smul,
    S.star_frequency_ground_dot_eta] at hpos
  simpa using hpos

theorem adjoint_cross_commutator (S : CCMParityFreeOddGroundData even odd) :
    S.frequencyᴴ * S.Qplus - S.Qminus * S.frequencyᴴ =
      Matrix.vecMulVec S.beta (star S.eta) := by
  have h := congrArg Matrix.conjTranspose S.cross_commutator
  simpa [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    S.plus_posSemidef.isHermitian.eq, S.minus_posSemidef.isHermitian.eq] using h

theorem squaredFrequency_commutator (S : CCMParityFreeOddGroundData even odd) :
    S.squaredFrequency * S.Qminus - S.Qminus * S.squaredFrequency =
      Matrix.vecMulVec S.beta (star S.delta) -
        Matrix.vecMulVec S.delta (star S.beta) := by
  have hcross : S.frequency * S.Qminus =
      S.Qplus * S.frequency - Matrix.vecMulVec S.eta (star S.beta) := by
    calc
      S.frequency * S.Qminus = S.Qplus * S.frequency -
          (S.Qplus * S.frequency - S.frequency * S.Qminus) := by abel
      _ = S.Qplus * S.frequency - Matrix.vecMulVec S.eta (star S.beta) := by
        rw [S.cross_commutator]
  have hadj : S.Qminus * S.frequencyᴴ =
      S.frequencyᴴ * S.Qplus - Matrix.vecMulVec S.beta (star S.eta) := by
    calc
      S.Qminus * S.frequencyᴴ = S.frequencyᴴ * S.Qplus -
          (S.frequencyᴴ * S.Qplus - S.Qminus * S.frequencyᴴ) := by abel
      _ = S.frequencyᴴ * S.Qplus - Matrix.vecMulVec S.beta (star S.eta) := by
        rw [S.adjoint_cross_commutator]
  rw [squaredFrequency]
  calc
    (S.frequencyᴴ * S.frequency) * S.Qminus -
        S.Qminus * (S.frequencyᴴ * S.frequency) =
      S.frequencyᴴ * (S.frequency * S.Qminus) -
        (S.Qminus * S.frequencyᴴ) * S.frequency := by
          simp only [Matrix.mul_assoc]
    _ = S.frequencyᴴ *
          (S.Qplus * S.frequency - Matrix.vecMulVec S.eta (star S.beta)) -
        (S.frequencyᴴ * S.Qplus - Matrix.vecMulVec S.beta (star S.eta)) *
          S.frequency := by rw [hcross, hadj]
    _ = Matrix.vecMulVec S.beta (star S.delta) -
        Matrix.vecMulVec S.delta (star S.beta) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec,
        Matrix.vecMulVec_mul]
      have hstarDelta : star S.delta = star S.eta ᵥ* S.frequency := by
        simp [delta, Matrix.star_mulVec]
      rw [hstarDelta]
      simp only [delta]
      simp only [← Matrix.mul_assoc]
      abel

theorem star_delta_dot_ground (S : CCMParityFreeOddGroundData even odd) :
    star S.delta ⬝ᵥ S.ground = 1 := by
  have hn : star S.ground ⬝ᵥ S.delta = 1 := by
    simpa [delta] using S.normalized
  have h := congrArg star hn
  rw [Matrix.star_dotProduct] at h
  rw [star_star] at h
  simpa using h

theorem qminus_mulVec_squaredFrequency_ground
    (S : CCMParityFreeOddGroundData even odd) :
    S.Qminus *ᵥ (S.squaredFrequency *ᵥ S.ground) =
      S.betaGround • S.delta - S.beta := by
  have h := congrArg (fun M : Matrix odd odd ℂ => M *ᵥ S.ground)
    S.squaredFrequency_commutator
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    S.ground_kernel, Matrix.mulVec_zero, zero_sub, Matrix.sub_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, S.star_delta_dot_ground] at h
  have hbeta : star S.beta ⬝ᵥ S.ground = S.betaGround := rfl
  rw [hbeta] at h
  simp only [op_smul_eq_smul, one_smul] at h
  have hn := congrArg Neg.neg h
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hn

theorem completion_metricAdjoint (S : CCMParityFreeOddGroundData even odd) :
    S.Qminus * S.completion = S.completionᴴ * S.Qminus := by
  let beta' : odd → ℂ := S.beta - S.betaGround • S.delta
  have hdisp : S.squaredFrequency * S.Qminus - S.Qminus * S.squaredFrequency =
      Matrix.vecMulVec beta' (star S.delta) -
        Matrix.vecMulVec S.delta (star beta') := by
    rw [S.squaredFrequency_commutator]
    ext i j
    simp [beta', Matrix.vecMulVec_apply]
    have hb : star S.betaGround = S.betaGround := by
      have hbim : S.betaGround.im = 0 :=
        (Complex.nonneg_iff.mp S.betaGround_pos.le).2.symm
      apply Complex.ext <;> simp [hbim]
    change (starRingEnd ℂ) S.betaGround = S.betaGround at hb
    rw [hb]
    ring
  have hboundary : S.Qminus *ᵥ (S.squaredFrequency *ᵥ S.ground) = -beta' := by
    rw [S.qminus_mulVec_squaredFrequency_ground]
    simp [beta']
  exact ccmSourceCompletion_metricAdjoint S.Qminus S.squaredFrequency S.delta beta'
    S.ground S.minus_posSemidef.isHermitian
    (Matrix.isHermitian_conjTranspose_mul_self S.frequency) hdisp hboundary

theorem qminus_mul_completion_eq (S : CCMParityFreeOddGroundData even odd) :
    S.Qminus * S.completion =
      S.frequencyᴴ * S.Qplus * S.frequency -
        S.betaGround • Matrix.vecMulVec S.delta (star S.delta) := by
  have hQB : S.Qminus * S.frequencyᴴ =
      S.frequencyᴴ * S.Qplus - Matrix.vecMulVec S.beta (star S.eta) := by
    calc
      S.Qminus * S.frequencyᴴ = S.frequencyᴴ * S.Qplus -
          (S.frequencyᴴ * S.Qplus - S.Qminus * S.frequencyᴴ) := by abel
      _ = S.frequencyᴴ * S.Qplus - Matrix.vecMulVec S.beta (star S.eta) := by
        rw [S.adjoint_cross_commutator]
  calc
    S.Qminus * S.completion =
        S.Qminus * S.squaredFrequency -
          Matrix.vecMulVec
            (S.Qminus *ᵥ (S.squaredFrequency *ᵥ S.ground)) (star S.delta) := by
      rw [completion, ccmSourceCompletion, Matrix.mul_sub, Matrix.mul_vecMulVec]
    _ = S.Qminus * S.squaredFrequency -
          Matrix.vecMulVec (S.betaGround • S.delta - S.beta) (star S.delta) := by
      rw [S.qminus_mulVec_squaredFrequency_ground]
    _ = (S.frequencyᴴ * S.Qplus - Matrix.vecMulVec S.beta (star S.eta)) *
          S.frequency -
          Matrix.vecMulVec (S.betaGround • S.delta - S.beta) (star S.delta) := by
      rw [squaredFrequency, ← Matrix.mul_assoc, hQB]
    _ = S.frequencyᴴ * S.Qplus * S.frequency -
          S.betaGround • Matrix.vecMulVec S.delta (star S.delta) := by
      ext i j
      have hstarDelta : star S.delta = star S.eta ᵥ* S.frequency := by
        simp [delta, Matrix.star_mulVec]
      simp [Matrix.sub_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_apply,
        hstarDelta]
      ring

theorem frequency_ground_semimetric_energy
    (S : CCMParityFreeOddGroundData even odd) :
    star (S.frequency *ᵥ S.ground) ⬝ᵥ
        (S.Qplus *ᵥ (S.frequency *ᵥ S.ground)) = S.betaGround := by
  rw [S.qplus_mulVec_frequency_ground, dotProduct_smul,
    S.star_frequency_ground_dot_eta]
  simp

theorem frequency_ground_semimetric_pairing
    (S : CCMParityFreeOddGroundData even odd) (f : odd → ℂ) :
    star (S.frequency *ᵥ S.ground) ⬝ᵥ
        (S.Qplus *ᵥ (S.frequency *ᵥ f)) =
      S.betaGround * (star S.delta ⬝ᵥ f) := by
  have hherm := ccmHermitian_mulVec_inner S.Qplus
    (S.frequency *ᵥ S.ground) (S.frequency *ᵥ f) S.plus_posSemidef.isHermitian
  rw [S.qplus_mulVec_frequency_ground] at hherm
  have hbstar : star S.betaGround = S.betaGround := by
    have hbim : S.betaGround.im = 0 :=
      (Complex.nonneg_iff.mp S.betaGround_pos.le).2.symm
    apply Complex.ext <;> simp [hbim]
  have hdelta : star S.eta ⬝ᵥ (S.frequency *ᵥ f) = star S.delta ⬝ᵥ f := by
    have hstarDelta : star S.delta = star S.eta ᵥ* S.frequency := by
      simp [delta, Matrix.star_mulVec]
    rw [hstarDelta, Matrix.dotProduct_mulVec]
  rw [star_smul, hbstar, smul_dotProduct, hdelta] at hherm
  simpa [smul_eq_mul] using hherm.symm

theorem betaGround_mul_norm_pairing_sq_le
    (S : CCMParityFreeOddGroundData even odd) (f : odd → ℂ) :
    S.betaGround.re * ‖star S.delta ⬝ᵥ f‖ ^ 2 ≤
      (star (S.frequency *ᵥ f) ⬝ᵥ
        (S.Qplus *ᵥ (S.frequency *ᵥ f))).re := by
  have hcs := norm_semimetric_pairing_sq_le S.Qplus S.plus_posSemidef
    (S.frequency *ᵥ S.ground) (S.frequency *ᵥ f)
  rw [S.frequency_ground_semimetric_pairing,
    S.frequency_ground_semimetric_energy] at hcs
  have hbRe : 0 < S.betaGround.re := (Complex.pos_iff.mp S.betaGround_pos).1
  have hbIm : S.betaGround.im = 0 := (Complex.pos_iff.mp S.betaGround_pos).2.symm
  have hbReal : S.betaGround = (S.betaGround.re : ℂ) := by
    apply Complex.ext <;> simp [hbIm]
  have hbNorm : ‖S.betaGround‖ = S.betaGround.re := by
    rw [hbReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbRe]
    simp
  rw [norm_mul, hbNorm, pow_two] at hcs
  nlinarith

theorem completion_metric_quadratic_re_nonneg
    (S : CCMParityFreeOddGroundData even odd) (f : odd → ℂ) :
    0 ≤ (star f ⬝ᵥ ((S.Qminus * S.completion) *ᵥ f)).re := by
  have hfreq (y : even → ℂ) :
      star f ⬝ᵥ (S.frequencyᴴ *ᵥ y) =
        star (S.frequency *ᵥ f) ⬝ᵥ y := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  let p : ℂ := star S.delta ⬝ᵥ f
  have hpstar : star f ⬝ᵥ S.delta = star p := by
    dsimp [p]
    rw [Matrix.star_dotProduct]
    change (starRingEnd ℂ) (star S.delta ⬝ᵥ f) =
      (starRingEnd ℂ) (star S.delta ⬝ᵥ f)
    rfl
  have hquad :
      star f ⬝ᵥ ((S.Qminus * S.completion) *ᵥ f) =
        star (S.frequency *ᵥ f) ⬝ᵥ
            (S.Qplus *ᵥ (S.frequency *ᵥ f)) -
          S.betaGround * star p * p := by
    rw [S.qminus_mul_completion_eq, Matrix.sub_mulVec,
      Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      Matrix.vecMulVec_mulVec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfreq]
    simp only [op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
    rw [hpstar]
    simp only [p]
    ring
  rw [hquad, Complex.sub_re]
  have hbIm : S.betaGround.im = 0 :=
    (Complex.pos_iff.mp S.betaGround_pos).2.symm
  have hbReal : S.betaGround = (S.betaGround.re : ℂ) := by
    apply Complex.ext <;> simp [hbIm]
  have hcorr : (S.betaGround * star p * p).re =
      S.betaGround.re * ‖p‖ ^ 2 := by
    have hscalar : (S.betaGround * star p * p).re =
        S.betaGround.re * (star p * p).re := by
      rw [hbReal]
      simp [Complex.mul_re]
      ring
    have hstarMul : (star p * p).re = Complex.normSq p := by
      simp [Complex.mul_re, Complex.normSq_apply]
    rw [hscalar, hstarMul, ← Complex.sq_norm]
  rw [hcorr]
  exact sub_nonneg.mpr (S.betaGround_mul_norm_pairing_sq_le f)

theorem qminus_mul_completion_posSemidef
    (S : CCMParityFreeOddGroundData even odd) :
    (S.Qminus * S.completion).PosSemidef := by
  have hherm : (S.Qminus * S.completion).IsHermitian := by
    show (S.Qminus * S.completion)ᴴ = S.Qminus * S.completion
    rw [Matrix.conjTranspose_mul, S.minus_posSemidef.isHermitian.eq]
    exact S.completion_metricAdjoint.symm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
  intro f
  apply Complex.nonneg_iff.mpr
  refine ⟨S.completion_metric_quadratic_re_nonneg f, ?_⟩
  exact (hherm.im_star_dotProduct_mulVec_self f).symm

theorem ground_riesz
    (S : CCMParityFreeOddGroundData even odd) (v : odd → ℂ)
    (hv : S.Qminus *ᵥ v = 0) :
    star S.ground ⬝ᵥ v =
      (star S.ground ⬝ᵥ S.ground) * (star S.delta ⬝ᵥ v) := by
  obtain ⟨a, rfl⟩ := S.ground_radical v hv
  rw [dotProduct_smul, dotProduct_smul, S.star_delta_dot_ground]
  ring

theorem completion_charpoly_zero_im_eq_zero
    (S : CCMParityFreeOddGroundData even odd) {z : ℂ}
    (hz : S.completion.charpoly.eval z = 0) :
    z.im = 0 := by
  exact ccmSourceCompletion_charpoly_zero_im_eq_zero
    S.Qminus S.squaredFrequency S.ground S.delta
    S.minus_posSemidef
    (Matrix.isHermitian_conjTranspose_mul_self S.frequency)
    S.star_delta_dot_ground S.ground_riesz S.completion_metricAdjoint hz

theorem completion_charpoly_zero_re_nonneg
    (S : CCMParityFreeOddGroundData even odd) {z : ℂ}
    (hz : S.completion.charpoly.eval z = 0) :
    0 ≤ z.re := by
  have hroot : S.completion.charpoly.IsRoot z := hz
  have hspec : z ∈ spectrum ℂ S.completion :=
    Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have hspeclin : z ∈ spectrum ℂ S.completion.toLin' := by
    simpa using hspec
  have heig : Module.End.HasEigenvalue S.completion.toLin' z :=
    Module.End.HasEigenvalue.of_mem_spectrum hspeclin
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hAv : S.completion *ᵥ v = z • v := by
    simpa using hv.apply_eq_smul
  have hvne : v ≠ 0 := hv.2
  let q : ℂ := star v ⬝ᵥ (S.Qminus *ᵥ v)
  have hqnonneg : 0 ≤ q := by
    exact S.minus_posSemidef.dotProduct_mulVec_nonneg v
  by_cases hqzero : q = 0
  · have hQv : S.Qminus *ᵥ v = 0 :=
      (S.minus_posSemidef.dotProduct_mulVec_zero_iff v).mp hqzero
    obtain ⟨a, hva⟩ := S.ground_radical v hQv
    have hAc : S.completion *ᵥ S.ground = 0 :=
      ccmSourceCompletion_mulVec_c S.squaredFrequency S.ground S.delta
        S.star_delta_dot_ground
    have hAvzero : S.completion *ᵥ v = 0 := by
      rw [hva, Matrix.mulVec_smul, hAc]
      simp
    have hzv : z • v = 0 := by rw [← hAv]; exact hAvzero
    have hz0 : z = 0 := (smul_eq_zero.mp hzv).resolve_right hvne
    simp [hz0]
  · have hqParts := Complex.nonneg_iff.mp hqnonneg
    have hqIm : q.im = 0 := hqParts.2.symm
    have hqRePos : 0 < q.re := by
      have hqReNe : q.re ≠ 0 := by
        intro hre
        apply hqzero
        apply Complex.ext
        · simpa using hre
        · simpa using hqIm
      exact lt_of_le_of_ne hqParts.1 (Ne.symm hqReNe)
    have hquad :
        star v ⬝ᵥ ((S.Qminus * S.completion) *ᵥ v) = z * q := by
      rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, dotProduct_smul]
      rfl
    have hpositive := S.qminus_mul_completion_posSemidef.dotProduct_mulVec_nonneg v
    rw [hquad] at hpositive
    have hre := (Complex.nonneg_iff.mp hpositive).1
    rw [Complex.mul_re, hqIm, mul_zero, sub_zero] at hre
    exact nonneg_of_mul_nonneg_left hre hqRePos

/-- Polynomial-times-resolvent numerator in the squared odd frequency variable. -/
def squaredResolventNumerator
    (S : CCMParityFreeOddGroundData even odd) (s : ℂ) : ℂ :=
  (S.squaredFrequency - s • (1 : Matrix odd odd ℂ)).det *
    (star S.delta ⬝ᵥ
      ((S.squaredFrequency - s • (1 : Matrix odd odd ℂ))⁻¹ *ᵥ S.ground))

theorem squaredResolventNumerator_zero_nonnegative_real
    (S : CCMParityFreeOddGroundData even odd) {s : ℂ}
    (hregular : IsUnit
      (S.squaredFrequency - s • (1 : Matrix odd odd ℂ)).det)
    (hz : S.squaredResolventNumerator s = 0) :
    s.im = 0 ∧ 0 ≤ s.re := by
  have hdetIdentity := ccmSourceCompletion_shift_det_eq_neg_mul_resolvent
    S.squaredFrequency S.ground S.delta s S.star_delta_dot_ground hregular
  have hcompletionDet :
      (S.completion - s • (1 : Matrix odd odd ℂ)).det = 0 := by
    change (ccmSourceCompletion S.squaredFrequency S.ground S.delta -
      s • (1 : Matrix odd odd ℂ)).det = 0
    rw [hdetIdentity]
    calc
      -s * (S.squaredFrequency - s • (1 : Matrix odd odd ℂ)).det *
          (star S.delta ⬝ᵥ
            ((S.squaredFrequency - s • (1 : Matrix odd odd ℂ))⁻¹ *ᵥ S.ground)) =
          -s * S.squaredResolventNumerator s := by
            simp [squaredResolventNumerator, mul_assoc]
      _ = 0 := by rw [hz, mul_zero]
  have heval : S.completion.charpoly.eval s = 0 := by
    rw [Matrix.eval_charpoly]
    have hneg :
        Matrix.scalar odd s - S.completion =
          -(S.completion - s • (1 : Matrix odd odd ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [hneg, Matrix.det_neg, hcompletionDet, mul_zero]
  exact ⟨S.completion_charpoly_zero_im_eq_zero heval,
    S.completion_charpoly_zero_re_nonneg heval⟩

/-- Squared-frequency resolvent numerator evaluated at the Fourier variable squared. -/
def oddFourierResolventNumerator
    (S : CCMParityFreeOddGroundData even odd) (z : ℂ) : ℂ :=
  S.squaredResolventNumerator (z ^ 2)

theorem oddFourierResolventNumerator_zero_im_eq_zero
    (S : CCMParityFreeOddGroundData even odd) {z : ℂ}
    (hregular : IsUnit
      (S.squaredFrequency - z ^ 2 • (1 : Matrix odd odd ℂ)).det)
    (hz : S.oddFourierResolventNumerator z = 0) :
    z.im = 0 := by
  have hs := S.squaredResolventNumerator_zero_nonnegative_real hregular
    (by simpa [oddFourierResolventNumerator] using hz)
  have hsim := hs.1
  have hsre := hs.2
  simp [Complex.mul_re, Complex.mul_im, pow_two] at hsim hsre
  have hxy : z.re * z.im = 0 := by nlinarith
  rcases mul_eq_zero.mp hxy with hx | hy
  · rw [hx] at hsre
    nlinarith [sq_nonneg z.im]
  · exact hy

end CCMParityFreeOddGroundData

end

end RHTower
