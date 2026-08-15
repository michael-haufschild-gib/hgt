import GaloisForLFunctions.HTGeometry.ProjectiveBallVolume
import GaloisForLFunctions.HTGeometry.ParameterCoverageBarrier
import GaloisForLFunctions.HTGeometry.GappedEigenlineTimeUniformFloor
import GaloisForLFunctions.HTGeometry.ObserverInvisibleTubeShortcut

/-!
# The parameter--time--coverage barrier for static ensembles

A bounded parameter set carries a net whose size is controlled by the parameter count and the
Lipschitz constant, and the image of that net covers any target the image is dense in, at twice the
density radius.

Projective space has uniform ball measure equal to the radius raised to twice the complex
codimension, so any cover needs at least that many balls.  Comparing the two counts bounds the
Lipschitz constant of a bounded parameter family from below by the projective covering entropy.
-/

open Metric MeasureTheory Set
open RHTower HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Transfer

variable {n : ℕ}

/-- The pure-state trace distance in coordinates. -/
def traceDist (x y : Fin n → ℂ) : ℝ := Real.sqrt (1 - ‖innerC x y‖ ^ 2)

theorem sqNorm_eq_norm_toLp_sq (x : Fin n → ℂ) :
    sqNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  rfl

theorem innerC_eq_inner_toLp (x y : Fin n → ℂ) :
    innerC x y =
      (inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 y) : ℂ) := by
  rw [PiLp.inner_apply, innerC]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, mul_comm]

theorem traceDist_eq_pureStateTraceDistance (x y : Fin n → ℂ) :
    traceDist x y =
      pureStateTraceDistance (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 y) := by
  rw [traceDist, pureStateTraceDistance, innerC_eq_inner_toLp]

theorem sqNorm_eq_one_iff {x : Fin n → ℂ} :
    sqNorm x = 1 ↔ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ = 1 := by
  rw [sqNorm_eq_norm_toLp_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)), h]
  · intro h
    rw [h]
    norm_num

theorem traceDist_nonneg (x y : Fin n → ℂ) : 0 ≤ traceDist x y := Real.sqrt_nonneg _

theorem traceDist_triangle {x y z : Fin n → ℂ} (hx : sqNorm x = 1) (hy : sqNorm y = 1)
    (hz : sqNorm z = 1) : traceDist x z ≤ traceDist x y + traceDist y z := by
  rw [traceDist_eq_pureStateTraceDistance, traceDist_eq_pureStateTraceDistance,
    traceDist_eq_pureStateTraceDistance]
  exact pureStateTraceDistance_triangle _ _ _ (sqNorm_eq_one_iff.mp hx)
    (sqNorm_eq_one_iff.mp hy) (sqNorm_eq_one_iff.mp hz)

/-- A trace-distance bound is a bound on the projective deficit. -/
theorem traceDist_le_iff {x φ : Fin n → ℂ} (hφ : sqNorm φ = 1) (hx : sqNorm x = 1)
    {r : ℝ} (hr : 0 ≤ r) :
    traceDist x φ ≤ r ↔ 1 - ‖innerC x φ‖ ^ 2 ≤ r ^ 2 := by
  have hnn : 0 ≤ 1 - ‖innerC x φ‖ ^ 2 := by
    rw [innerC_eq_inner_toLp]
    have hcs := norm_inner_le_norm (𝕜 := ℂ)
      (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 φ)
    rw [sqNorm_eq_one_iff.mp hx, sqNorm_eq_one_iff.mp hφ] at hcs
    nlinarith [norm_nonneg
      (inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 φ) : ℂ), hcs]
  rw [traceDist]
  constructor
  · intro h
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (1 - ‖innerC x φ‖ ^ 2), h]
  · intro h
    calc Real.sqrt (1 - ‖innerC x φ‖ ^ 2) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt h
      _ = r := Real.sqrt_sq hr

theorem innerC_comm_norm (x y : Fin n → ℂ) : ‖innerC x y‖ = ‖innerC y x‖ := by
  rw [innerC_eq_inner_toLp, innerC_eq_inner_toLp, ← inner_conj_symm, RCLike.norm_conj]

end Transfer

section Barrier

variable {n m : ℕ}

/-- A trace-distance cover of projective space is a cone cover of the unit ball. -/
theorem cone_cover_of_traceDist_cover {r : ℝ} (hr : 0 ≤ r)
    (t : Finset (Fin (n + 1) → ℂ)) (hunit : ∀ φ ∈ t, sqNorm φ = 1)
    (hcover : ∀ ψ : Fin (n + 1) → ℂ, sqNorm ψ = 1 → ∃ φ ∈ t, traceDist ψ φ ≤ r) :
    ∀ x : Fin (n + 1) → ℂ, sqNorm x ≤ 1 →
      ∃ φ ∈ t, sqNorm x - ‖innerC φ x‖ ^ 2 ≤ r ^ 2 * sqNorm x := by
  intro x hx
  have hone : sqNorm (Pi.single 0 1 : Fin (n + 1) → ℂ) = 1 := by
    rw [sqNorm, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ 0) h
  rcases eq_or_ne (sqNorm x) 0 with hx0 | hx0
  · obtain ⟨φ, hφt, -⟩ := hcover (Pi.single 0 1) hone
    refine ⟨φ, hφt, ?_⟩
    rw [hx0]
    have : (0 : ℝ) ≤ ‖innerC φ x‖ ^ 2 := by positivity
    linarith
  · have hxpos : 0 < sqNorm x := lt_of_le_of_ne (sqNorm_nonneg x) (Ne.symm hx0)
    have hnorm : 0 < Real.sqrt (sqNorm x) := Real.sqrt_pos.mpr hxpos
    set ψ : Fin (n + 1) → ℂ := (Real.sqrt (sqNorm x))⁻¹ • x with hψ
    have hψnorm : sqNorm ψ = 1 := by
      rw [hψ, sqNorm_smul, inv_pow, Real.sq_sqrt hxpos.le, inv_mul_cancel₀ (ne_of_gt hxpos)]
    obtain ⟨φ, hφt, hφ⟩ := hcover ψ hψnorm
    refine ⟨φ, hφt, ?_⟩
    have hdef := (traceDist_le_iff (hunit φ hφt) hψnorm hr).mp hφ
    have hinner : innerC ψ φ = ((Real.sqrt (sqNorm x))⁻¹ : ℂ) * innerC x φ := by
      rw [hψ, innerC, innerC, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsmul : ((Real.sqrt (sqNorm x))⁻¹ • x) i =
          ((Real.sqrt (sqNorm x))⁻¹ : ℂ) * x i := by
        show ((Real.sqrt (sqNorm x))⁻¹ : ℝ) • x i = _
        rw [Complex.real_smul]
        push_cast
        ring
      rw [hsmul, map_mul, map_inv₀, Complex.conj_ofReal]
      ring
    have hnormeq : ‖innerC ψ φ‖ = (Real.sqrt (sqNorm x))⁻¹ * ‖innerC x φ‖ := by
      rw [hinner, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hnorm]
    rw [hnormeq] at hdef
    have hsq : ((Real.sqrt (sqNorm x))⁻¹ * ‖innerC x φ‖) ^ 2 = ‖innerC x φ‖ ^ 2 / sqNorm x := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hxpos.le]
      ring
    rw [hsq] at hdef
    have hmul := mul_le_mul_of_nonneg_right hdef hxpos.le
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hxpos), one_mul] at hmul
    rw [innerC_comm_norm]
    exact hmul

/-- **Static-ensemble coverage barrier.**  A bounded `m`-parameter Lipschitz family whose image is
`ε`-dense in projective space forces the parameter-to-resolution ratio to exceed the projective
covering entropy. -/
theorem one_le_pow_mul_pow (hn : 0 < n) (hm : 0 < m)
    {R L ε : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : 2 * ε < 1)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : K ⊆ closedBall 0 R)
    (F : EuclideanSpace ℝ (Fin m) → (Fin (n + 1) → ℂ))
    (hunit : ∀ θ, sqNorm (F θ) = 1)
    (hlip : ∀ θ ∈ K, ∀ η ∈ K, traceDist (F θ) (F η) ≤ L * dist θ η)
    (hdense : ∀ ψ : Fin (n + 1) → ℂ, sqNorm ψ = 1 → ∃ θ ∈ K, traceDist ψ (F θ) ≤ ε) :
    1 ≤ (1 + 2 * R * L / ε) ^ m * (2 * ε) ^ (2 * n) := by
  classical
  have hone : sqNorm (Pi.single 0 1 : Fin (n + 1) → ℂ) = 1 := by
    rw [sqNorm, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj]
      simp
    · intro h
      exact absurd (Finset.mem_univ 0) h
  obtain ⟨T, hTK, hTcard, hTnet⟩ :
      ∃ T : Finset (EuclideanSpace ℝ (Fin m)), (↑T ⊆ K) ∧
        (T.card : ℝ) ≤ (1 + 2 * R * L / ε) ^ m ∧
        ∀ θ ∈ K, ∃ τ ∈ T, traceDist (F θ) (F τ) ≤ ε := by
    rcases eq_or_lt_of_le hL with hL0 | hLpos
    · obtain ⟨θ₀, hθ₀, -⟩ := hdense (Pi.single 0 1) hone
      refine ⟨{θ₀}, by simpa using hθ₀, ?_, ?_⟩
      · rw [Finset.card_singleton]
        have h1 : (1 : ℝ) ≤ 1 + 2 * R * L / ε := by
          rw [← hL0]
          simp
        calc ((1 : ℕ) : ℝ) = 1 ^ m := by norm_num
          _ ≤ (1 + 2 * R * L / ε) ^ m := pow_le_pow_left₀ (by norm_num) h1 m
      · intro θ hθ
        refine ⟨θ₀, Finset.mem_singleton_self _, ?_⟩
        refine le_trans (hlip θ hθ θ₀ hθ₀) ?_
        rw [← hL0, zero_mul]
        exact hε.le
    · set δ : ℝ := ε / L with hδdef
      have hδ : 0 < δ := div_pos hε hLpos
      obtain ⟨T, hTK, hTcard, hTnet⟩ := exists_separated_net hm hδ hR K hK
      refine ⟨T, hTK, ?_, ?_⟩
      · have hδm : (0 : ℝ) < (δ / 2) ^ m := by positivity
        have hcard : (T.card : ℝ) ≤ ((R + δ / 2) / (δ / 2)) ^ m := by
          rw [div_pow, le_div_iff₀ hδm]
          exact hTcard
        refine le_trans hcard (le_of_eq ?_)
        congr 1
        rw [hδdef]
        field_simp
        ring
      · intro θ hθ
        obtain ⟨τ, hτ, hτd⟩ := hTnet θ hθ
        refine ⟨τ, hτ, ?_⟩
        refine le_trans (hlip θ hθ τ (hTK hτ)) ?_
        have hstep : L * dist θ τ ≤ L * δ := mul_le_mul_of_nonneg_left hτd.le hL
        rw [hδdef] at hstep
        calc L * dist θ τ ≤ L * (ε / L) := hstep
          _ = ε := by field_simp
  set t : Finset (Fin (n + 1) → ℂ) := T.image F with ht
  have htunit : ∀ φ ∈ t, sqNorm φ = 1 := by
    intro φ hφ
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hφ
    exact hunit τ
  have hcover : ∀ ψ : Fin (n + 1) → ℂ, sqNorm ψ = 1 →
      ∃ φ ∈ t, traceDist ψ φ ≤ 2 * ε := by
    intro ψ hψ
    obtain ⟨θ, hθ, hθd⟩ := hdense ψ hψ
    obtain ⟨τ, hτ, hτd⟩ := hTnet θ hθ
    refine ⟨F τ, Finset.mem_image_of_mem F hτ, ?_⟩
    calc traceDist ψ (F τ) ≤ traceDist ψ (F θ) + traceDist (F θ) (F τ) :=
          traceDist_triangle hψ (hunit θ) (hunit τ)
      _ ≤ ε + ε := add_le_add hθd hτd
      _ = 2 * ε := by ring
  have hconecover := cone_cover_of_traceDist_cover (by positivity) t htunit hcover
  have hmain := one_le_card_mul_pow hn (r := 2 * ε) (by positivity) hε1 t htunit hconecover
  have htcard : (t.card : ℝ) ≤ (1 + 2 * R * L / ε) ^ m :=
    le_trans (Nat.cast_le.mpr Finset.card_image_le) hTcard
  have hpos : (0 : ℝ) ≤ (2 * ε) ^ (2 * n) := by positivity
  calc (1 : ℝ) ≤ (t.card : ℝ) * (2 * ε) ^ (2 * n) := hmain
    _ ≤ (1 + 2 * R * L / ε) ^ m * (2 * ε) ^ (2 * n) :=
        mul_le_mul_of_nonneg_right htcard hpos

end Barrier

section Concrete

open QuantumAlg
open scoped Matrix Matrix.Norms.L2Operator

variable {n M : ℕ}

/-- The interaction scale of a Hermitian dictionary. -/
def dictionaryScale (A : Fin M → Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ a, ‖A a‖ ^ 2)

theorem dictionaryScale_nonneg (A : Fin M → Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ dictionaryScale A := Real.sqrt_nonneg _

/-- **Cauchy--Schwarz in coefficient space.**  A real linear combination of a Hermitian dictionary
is Lipschitz in the coefficients with the dictionary scale. -/
theorem norm_generatorCombination_sub_le (A : Fin M → Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin M → ℝ) :
    ‖generatorCombination A x - generatorCombination A y‖ ≤
      dictionaryScale A * Real.sqrt (∑ a, (x a - y a) ^ 2) := by
  classical
  have hdiff : generatorCombination A x - generatorCombination A y =
      ∑ a, ((x a - y a : ℝ) : ℂ) • A a := by
    rw [generatorCombination, generatorCombination, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ a : Fin M, ‖((x a - y a : ℝ) : ℂ) • A a‖ = |x a - y a| * ‖A a‖ := by
    intro a
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.sum_congr rfl fun a _ => hterm a]
  have hcs : (∑ a, |x a - y a| * ‖A a‖) ^ 2 ≤
      (∑ a, |x a - y a| ^ 2) * ∑ a, ‖A a‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have habs : ∀ a : Fin M, |x a - y a| ^ 2 = (x a - y a) ^ 2 := fun a => sq_abs _
  rw [Finset.sum_congr rfl fun a _ => habs a] at hcs
  have hnn1 : (0 : ℝ) ≤ ∑ a, (x a - y a) ^ 2 := Finset.sum_nonneg fun a _ => by positivity
  have hnn2 : (0 : ℝ) ≤ ∑ a, ‖A a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
  have hlhs : (0 : ℝ) ≤ ∑ a, |x a - y a| * ‖A a‖ :=
    Finset.sum_nonneg fun a _ => by positivity
  have hrhs : dictionaryScale A * Real.sqrt (∑ a, (x a - y a) ^ 2) =
      Real.sqrt ((∑ a, (x a - y a) ^ 2) * ∑ a, ‖A a‖ ^ 2) := by
    rw [dictionaryScale, ← Real.sqrt_mul hnn2, mul_comm]
  rw [hrhs]
  calc (∑ a, |x a - y a| * ‖A a‖)
      = Real.sqrt ((∑ a, |x a - y a| * ‖A a‖) ^ 2) := (Real.sqrt_sq hlhs).symm
    _ ≤ Real.sqrt ((∑ a, (x a - y a) ^ 2) * ∑ a, ‖A a‖ ^ 2) := Real.sqrt_le_sqrt hcs


theorem traceDist_le_norm_sub {x y : Fin n → ℂ} (hx : sqNorm x = 1) (hy : sqNorm y = 1) :
    traceDist x y ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)) - WithLp.toLp 2 y‖ := by
  set X : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x with hXdef
  set Y : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 y with hYdef
  have hX : ‖X‖ = 1 := sqNorm_eq_one_iff.mp hx
  have hY : ‖Y‖ = 1 := sqNorm_eq_one_iff.mp hy
  have hexp : ‖X - Y‖ ^ 2 = 2 - 2 * RCLike.re (inner ℂ X Y : ℂ) := by
    rw [norm_sub_sq (𝕜 := ℂ), hX, hY]
    ring
  have hre : RCLike.re (inner ℂ X Y : ℂ) ≤ ‖(inner ℂ X Y : ℂ)‖ := RCLike.re_le_norm _
  have hc : ‖(inner ℂ X Y : ℂ)‖ ≤ 1 := by
    have hcs := norm_inner_le_norm (𝕜 := ℂ) X Y
    rw [hX, hY] at hcs
    simpa using hcs
  have hkey : 1 - ‖innerC x y‖ ^ 2 ≤ ‖X - Y‖ ^ 2 := by
    rw [innerC_eq_inner_toLp, ← hXdef, ← hYdef]
    nlinarith [hexp, hre, hc, norm_nonneg (inner ℂ X Y : ℂ)]
  rw [traceDist]
  calc Real.sqrt (1 - ‖innerC x y‖ ^ 2) ≤ Real.sqrt (‖X - Y‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖X - Y‖ := Real.sqrt_sq (norm_nonneg _)

/-- The seed evolved by a coefficient-linear Hamiltonian. -/
def evolvedSeed (A : Fin M → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (χ : Fin (n + 1) → ℂ)
    (t : ℝ) (θ : EuclideanSpace ℝ (Fin M)) : Fin (n + 1) → ℂ :=
  (unitaryEvolution (generatorCombination A θ.ofLp) t).mulVec χ

theorem sqNorm_evolvedSeed {A : Fin M → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : ∀ a, (A a)ᴴ = A a) (χ : Fin (n + 1) → ℂ) (t : ℝ)
    (θ : EuclideanSpace ℝ (Fin M)) :
    sqNorm (evolvedSeed A χ t θ) = sqNorm χ := by
  have hself : IsSelfAdjoint (generatorCombination A θ.ofLp) :=
    generatorCombination_conjTranspose hA θ.ofLp
  have hmem := unitaryEvolution_mem_unitary hself t
  have hU : (unitaryEvolution (generatorCombination A θ.ofLp) t)ᴴ *
      unitaryEvolution (generatorCombination A θ.ofLp) t = 1 := by
    have := hmem.1
    rwa [Matrix.star_eq_conjTranspose] at this
  exact sqNorm_mulVec hU χ

theorem traceDist_evolvedSeed_le {A : Fin M → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : ∀ a, (A a)ᴴ = A a) {χ : Fin (n + 1) → ℂ} (hχ : sqNorm χ = 1) (t : ℝ)
    (θ η : EuclideanSpace ℝ (Fin M)) :
    traceDist (evolvedSeed A χ t θ) (evolvedSeed A χ t η) ≤
      (|t| * dictionaryScale A) * dist θ η := by
  have hunitθ : sqNorm (evolvedSeed A χ t θ) = 1 := by
    rw [sqNorm_evolvedSeed hA, hχ]
  have hunitη : sqNorm (evolvedSeed A χ t η) = 1 := by
    rw [sqNorm_evolvedSeed hA, hχ]
  refine le_trans (traceDist_le_norm_sub hunitθ hunitη) ?_
  have hχnorm : ‖(WithLp.toLp 2 χ : EuclideanSpace ℂ (Fin (n + 1)))‖ = 1 :=
    sqNorm_eq_one_iff.mp hχ
  have hstep := QuantumAlg.norm_unitaryEvolution_mulVec_sub_le
    (H := generatorCombination A θ.ofLp) (K := generatorCombination A η.ofLp)
    (generatorCombination_conjTranspose hA θ.ofLp)
    (generatorCombination_conjTranspose hA η.ofLp) t
    (WithLp.toLp 2 χ : EuclideanSpace ℂ (Fin (n + 1)))
  rw [hχnorm, mul_one] at hstep
  refine le_trans hstep ?_
  have hgen := norm_generatorCombination_sub_le A θ.ofLp η.ofLp
  have hdist : dist θ η = Real.sqrt (∑ a, (θ.ofLp a - η.ofLp a) ^ 2) := by
    rw [EuclideanSpace.dist_eq]
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun a _ => ?_)
    rw [Real.dist_eq, sq_abs]
  rw [hdist, mul_assoc]
  exact mul_le_mul_of_nonneg_left hgen (abs_nonneg t)

/-- **Static-Hamiltonian coverage time.**  A bounded `M`-parameter self-adjoint ensemble whose
propagated seed is `ε`-dense in projective space obeys the parameter--time--coverage barrier. -/
theorem coverage_time_barrier (hn : 0 < n) (hM : 0 < M)
    {A : Fin M → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : ∀ a, (A a)ᴴ = A a)
    {χ : Fin (n + 1) → ℂ} (hχ : sqNorm χ = 1)
    {R ε t : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : 2 * ε < 1)
    {K : Set (EuclideanSpace ℝ (Fin M))} (hK : K ⊆ closedBall 0 R)
    (hdense : ∀ ψ : Fin (n + 1) → ℂ, sqNorm ψ = 1 →
      ∃ θ ∈ K, traceDist ψ (evolvedSeed A χ t θ) ≤ ε) :
    1 ≤ (1 + 2 * R * (|t| * dictionaryScale A) / ε) ^ M * (2 * ε) ^ (2 * n) := by
  refine one_le_pow_mul_pow hn hM hR
    (mul_nonneg (abs_nonneg t) (dictionaryScale_nonneg A)) hε hε1 hK (evolvedSeed A χ t)
    (fun θ => by rw [sqNorm_evolvedSeed hA, hχ]) ?_ hdense
  intro θ _ η _
  exact traceDist_evolvedSeed_le hA hχ t θ η

/-- **Coverage time lower bound.**  Projective `ε`-density of a bounded `M`-parameter static
ensemble forces the elapsed action to exceed the `M`-th root of the projective covering number. -/
theorem coverage_time_lower_bound (hn : 0 < n) (hM : 0 < M)
    {A : Fin M → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : ∀ a, (A a)ᴴ = A a)
    {χ : Fin (n + 1) → ℂ} (hχ : sqNorm χ = 1)
    {R ε t : ℝ} (hR : 0 < R) (hε : 0 < ε) (hε1 : 2 * ε < 1)
    {K : Set (EuclideanSpace ℝ (Fin M))} (hK : K ⊆ closedBall 0 R)
    (hdense : ∀ ψ : Fin (n + 1) → ℂ, sqNorm ψ = 1 →
      ∃ θ ∈ K, traceDist ψ (evolvedSeed A χ t θ) ≤ ε) :
    ε / (2 * R) * ((2 * ε) ^ (-(2 * (n : ℝ)) / (M : ℝ)) - 1) ≤ |t| * dictionaryScale A := by
  have h2ε : (0 : ℝ) < 2 * ε := by linarith
  have hpow : (0 : ℝ) < (2 * ε) ^ (2 * n) := by positivity
  have hbar := coverage_time_barrier hn hM hA hχ hR.le hε hε1 hK hdense
  set L : ℝ := |t| * dictionaryScale A with hL
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact mul_nonneg (abs_nonneg t) (dictionaryScale_nonneg A)
  have hcnn : (0 : ℝ) ≤ 2 * R * L / ε := by positivity
  have hinv : ((2 * ε) ^ (2 * n))⁻¹ ≤ (1 + 2 * R * L / ε) ^ M := by
    have hstep := mul_le_mul_of_nonneg_right hbar (le_of_lt (inv_pos.mpr hpow))
    rw [one_mul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hpow), mul_one] at hstep
    exact hstep
  have hroot := rpow_inv_le_of_le_pow hM (by positivity) hcnn hinv
  have hrw : (((2 * ε) ^ (2 * n))⁻¹ : ℝ) ^ ((M : ℝ)⁻¹) =
      (2 * ε) ^ (-(2 * (n : ℝ)) / (M : ℝ)) := by
    rw [← Real.rpow_natCast (2 * ε) (2 * n), ← Real.rpow_neg h2ε.le, ← Real.rpow_mul h2ε.le]
    congr 1
    push_cast
    ring
  rw [hrw] at hroot
  have h2R : (0 : ℝ) < 2 * R := by linarith
  have hfrac : (0 : ℝ) < ε / (2 * R) := div_pos hε h2R
  have hsub : (2 * ε) ^ (-(2 * (n : ℝ)) / (M : ℝ)) - 1 ≤ 2 * R * L / ε := by linarith
  calc ε / (2 * R) * ((2 * ε) ^ (-(2 * (n : ℝ)) / (M : ℝ)) - 1)
      ≤ ε / (2 * R) * (2 * R * L / ε) := mul_le_mul_of_nonneg_left hsub hfrac.le
    _ = L := by field_simp

theorem dictionaryScale_le_sqrt {M : ℕ} {N : ℕ} (A : Fin M → Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ a, ‖A a‖ ≤ 1) {c : ℝ} (hc : (M : ℝ) ≤ c) : dictionaryScale A ≤ Real.sqrt c := by
  refine Real.sqrt_le_sqrt ?_
  calc (∑ a, ‖A a‖ ^ 2) ≤ ∑ _a : Fin M, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        nlinarith [norm_nonneg (A a), hA a]
    _ = (M : ℝ) := by simp
    _ ≤ c := hc

/-- **Ordinary local shells miss Haar coverage until recurrence scale.**  On `k` qubits with at most
`12k` bounded self-adjoint controls in the unit parameter ball, projective `ε`-density forces an
elapsed action exponential in `2^k / k`. -/
theorem coverage_time_exponential {k M : ℕ} (hk : 1 ≤ k) (hM : 0 < M) (hMle : M ≤ 12 * k)
    {A : Fin M → Matrix (Fin (2 ^ k - 1 + 1)) (Fin (2 ^ k - 1 + 1)) ℂ}
    (hA : ∀ a, (A a)ᴴ = A a) (hAnorm : ∀ a, ‖A a‖ ≤ 1)
    {χ : Fin (2 ^ k - 1 + 1) → ℂ} (hχ : sqNorm χ = 1)
    {ε t : ℝ} (hε : 0 < ε) (hε1 : 2 * ε < 1)
    {K : Set (EuclideanSpace ℝ (Fin M))} (hK : K ⊆ closedBall 0 1)
    (hdense : ∀ ψ : Fin (2 ^ k - 1 + 1) → ℂ, sqNorm ψ = 1 →
      ∃ θ ∈ K, traceDist ψ (evolvedSeed A χ t θ) ≤ ε) :
    ε / 2 * (Real.exp (Real.log (1 / (2 * ε)) * 2 ^ k / (12 * k)) - 1) ≤
      |t| * Real.sqrt (12 * k) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h2ε : (0 : ℝ) < 2 * ε := by linarith
  have hpowk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hpowk2 : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hn : 0 < 2 ^ k - 1 := by
    have : 2 ≤ 2 ^ k := Nat.one_lt_two_pow_iff.mpr (by omega)
    omega
  have hbound := coverage_time_lower_bound hn hM hA hχ one_pos hε hε1 hK hdense
  have hscale : dictionaryScale A ≤ Real.sqrt (12 * (k : ℝ)) := by
    refine dictionaryScale_le_sqrt A hAnorm ?_
    have : (M : ℝ) ≤ ((12 * k : ℕ) : ℝ) := by exact_mod_cast hMle
    simpa using this
  have hcast : ((2 ^ k - 1 : ℕ) : ℝ) = 2 ^ k - 1 := by
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    push_cast [Nat.cast_sub h1]
    ring
  have hlog : 0 < Real.log (1 / (2 * ε)) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ h2ε, one_mul]
    exact hε1
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMle' : (M : ℝ) ≤ 12 * (k : ℝ) := by
    have : (M : ℝ) ≤ ((12 * k : ℕ) : ℝ) := by exact_mod_cast hMle
    simpa using this
  have hexpo : Real.log (1 / (2 * ε)) * 2 ^ k / (12 * (k : ℝ)) ≤
      -(2 * ((2 ^ k - 1 : ℕ) : ℝ)) / (M : ℝ) * Real.log (2 * ε) := by
    have hlogneg : Real.log (2 * ε) = -Real.log (1 / (2 * ε)) := by
      rw [Real.log_div one_ne_zero (ne_of_gt h2ε), Real.log_one]
      ring
    rw [hlogneg, hcast]
    have hratio : (2 : ℝ) ^ k / (12 * (k : ℝ)) ≤ 2 * (2 ^ k - 1) / (M : ℝ) := by
      have hnum : (2 : ℝ) ^ k ≤ 2 * (2 ^ k - 1) := by linarith
      have h12k : (0 : ℝ) < 12 * (k : ℝ) := by linarith
      rw [div_le_div_iff₀ h12k hMpos]
      nlinarith [hMle', hnum, hMpos, h12k, hpowk2]
    have hkey : Real.log (1 / (2 * ε)) * ((2 : ℝ) ^ k / (12 * (k : ℝ))) ≤
        Real.log (1 / (2 * ε)) * (2 * ((2 : ℝ) ^ k - 1) / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio hlog.le
    calc Real.log (1 / (2 * ε)) * 2 ^ k / (12 * (k : ℝ))
        = Real.log (1 / (2 * ε)) * ((2 : ℝ) ^ k / (12 * (k : ℝ))) := by ring
      _ ≤ Real.log (1 / (2 * ε)) * (2 * ((2 : ℝ) ^ k - 1) / (M : ℝ)) := hkey
      _ = -(2 * ((2 : ℝ) ^ k - 1)) / (M : ℝ) * -Real.log (1 / (2 * ε)) := by ring
  have hrpow : Real.exp (Real.log (1 / (2 * ε)) * 2 ^ k / (12 * (k : ℝ))) ≤
      (2 * ε) ^ (-(2 * ((2 ^ k - 1 : ℕ) : ℝ)) / (M : ℝ)) := by
    rw [Real.rpow_def_of_pos h2ε]
    refine Real.exp_le_exp.mpr ?_
    calc Real.log (1 / (2 * ε)) * 2 ^ k / (12 * (k : ℝ))
        ≤ -(2 * ((2 ^ k - 1 : ℕ) : ℝ)) / (M : ℝ) * Real.log (2 * ε) := hexpo
      _ = Real.log (2 * ε) * (-(2 * ((2 ^ k - 1 : ℕ) : ℝ)) / (M : ℝ)) := by ring
  have hchain : ε / 2 * (Real.exp (Real.log (1 / (2 * ε)) * 2 ^ k / (12 * (k : ℝ))) - 1) ≤
      |t| * dictionaryScale A := by
    have hstep : ε / 2 * (Real.exp (Real.log (1 / (2 * ε)) * 2 ^ k / (12 * (k : ℝ))) - 1) ≤
        ε / (2 * 1) * ((2 * ε) ^ (-(2 * ((2 ^ k - 1 : ℕ) : ℝ)) / (M : ℝ)) - 1) := by
      have h1 : (ε : ℝ) / 2 = ε / (2 * 1) := by norm_num
      rw [← h1]
      exact mul_le_mul_of_nonneg_left (by linarith [hrpow]) (by positivity)
    exact le_trans hstep hbound
  refine le_trans hchain ?_
  exact mul_le_mul_of_nonneg_left hscale (abs_nonneg t)

end Concrete

section OrbitNet

open QuantumAlg
open scoped Matrix Matrix.Norms.L2Operator

variable {N M : ℕ}

/-- **Coefficient entropy covers the fixed-time image.**  The time-`t` image of a bounded
coefficient set under a self-adjoint coefficient-linear Hamiltonian has an `ε`-net whose size is
bounded by the coefficient entropy alone, with no reference to Hilbert-space dimension. -/
theorem exists_orbit_net_card_le (hM : 0 < M)
    {A : Fin M → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hA : ∀ a, (A a)ᴴ = A a)
    {ψ₀ : EuclideanSpace ℂ (Fin (N + 1))} (hψ₀ : ‖ψ₀‖ = 1)
    {R ε t : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {K : Set (EuclideanSpace ℝ (Fin M))} (hK : K ⊆ closedBall 0 R) :
    ∃ s : Finset (EuclideanSpace ℂ (Fin (N + 1))),
      (fun θ : EuclideanSpace ℝ (Fin M) =>
          (WithLp.toLp 2 (evolvedSeed A ψ₀.ofLp t θ) : EuclideanSpace ℂ (Fin (N + 1)))) '' K ⊆
        (⋃ y ∈ s, closedBall y ε) ∧
      (s.card : ℝ) ≤ (1 + 2 * R * (|t| * dictionaryScale A) / ε) ^ M := by
  refine exists_image_net_card_le hM hR
    (mul_nonneg (abs_nonneg t) (dictionaryScale_nonneg A)) hε hK _ ?_
  intro θ _ η _
  have hstep := QuantumAlg.norm_unitaryEvolution_mulVec_sub_le
    (H := generatorCombination A θ.ofLp) (K := generatorCombination A η.ofLp)
    (generatorCombination_conjTranspose hA θ.ofLp)
    (generatorCombination_conjTranspose hA η.ofLp) t ψ₀
  rw [hψ₀, mul_one] at hstep
  have hgen := norm_generatorCombination_sub_le A θ.ofLp η.ofLp
  have hdist : dist θ η = Real.sqrt (∑ a, (θ.ofLp a - η.ofLp a) ^ 2) := by
    rw [EuclideanSpace.dist_eq]
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun a _ => ?_)
    rw [Real.dist_eq, sq_abs]
  rw [dist_eq_norm]
  refine le_trans hstep ?_
  rw [hdist, mul_assoc]
  exact mul_le_mul_of_nonneg_left hgen (abs_nonneg t)

/-- The logarithm of the coefficient-entropy net size. -/
theorem log_orbit_net_card_le (R L ε : ℝ) (M : ℕ) :
    Real.log ((1 + 2 * R * L / ε) ^ M) = (M : ℝ) * Real.log (1 + 2 * R * L / ε) := by
  rw [Real.log_pow]

/-- **Classical selector length cannot witness Brown complexity.**  With linearly many
coefficients, polynomially bounded coefficient scale, time at most `2^k` and fixed accuracy, the
logarithm of the net size is quadratic in the qubit number. -/
theorem log_orbit_net_card_quadratic {p : ℕ} {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k M : ℕ) (R L ε : ℝ), 1 ≤ k → M ≤ k → 0 ≤ R → 0 ≤ L →
      R * L ≤ (k : ℝ) ^ p * 2 ^ k → ε₀ ≤ ε →
      (M : ℝ) * Real.log (1 + 2 * R * L / ε) ≤ C * (k : ℝ) ^ 2 := by
  refine ⟨2 * Real.log 2 + |Real.log (2 / ε₀)| + (p : ℝ) + 1, by positivity, ?_⟩
  intro k M R L ε hk hMk hR hL hRL hε
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hMk' : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hMk
  have hεpos : 0 < ε := lt_of_lt_of_le hε₀ hε
  set y : ℝ := (2 / ε₀) * ((k : ℝ) ^ p * 2 ^ k) with hy
  have hypos : 0 < y := by
    rw [hy]
    positivity
  have harg : 1 + 2 * R * L / ε ≤ 1 + y := by
    have hnum : 2 * (R * L) ≤ 2 * ((k : ℝ) ^ p * 2 ^ k) := by linarith
    have hstep : 2 * R * L / ε ≤ y := by
      rw [hy]
      calc 2 * R * L / ε = (2 * (R * L)) / ε := by ring
        _ ≤ (2 * ((k : ℝ) ^ p * 2 ^ k)) / ε := by gcongr
        _ ≤ (2 * ((k : ℝ) ^ p * 2 ^ k)) / ε₀ := by gcongr
        _ = (2 / ε₀) * ((k : ℝ) ^ p * 2 ^ k) := by ring
    linarith
  have hposarg : (0 : ℝ) < 1 + 2 * R * L / ε := by positivity
  have hmono : Real.log (1 + 2 * R * L / ε) ≤ Real.log (1 + y) :=
    Real.log_le_log hposarg harg
  have hsplit : (1 : ℝ) + y ≤ 2 * max 1 y := by
    rcases le_total y 1 with h | h
    · rw [max_eq_left h]
      linarith
    · rw [max_eq_right h]
      linarith
  have hmaxpos : (0 : ℝ) < max 1 y := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hlog2 : Real.log (1 + y) ≤ Real.log 2 + Real.log (max 1 y) := by
    calc Real.log (1 + y) ≤ Real.log (2 * max 1 y) :=
          Real.log_le_log (by positivity) hsplit
      _ = Real.log 2 + Real.log (max 1 y) := Real.log_mul (by norm_num) (ne_of_gt hmaxpos)
  have hmaxle : Real.log (max 1 y) ≤ |Real.log y| := by
    rcases le_total y 1 with h | h
    · rw [max_eq_left h, Real.log_one]
      positivity
    · rw [max_eq_right h]
      exact le_abs_self _
  have hlogy : Real.log y = Real.log (2 / ε₀) + (p : ℝ) * Real.log (k : ℝ) +
      (k : ℝ) * Real.log 2 := by
    rw [hy, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hlogkle : Real.log (k : ℝ) ≤ (k : ℝ) := by
    have := Real.log_le_sub_one_of_pos hkpos
    linarith
  have habs : |Real.log y| ≤ |Real.log (2 / ε₀)| + (p : ℝ) * (k : ℝ) + (k : ℝ) * Real.log 2 := by
    rw [hlogy]
    refine le_trans (abs_add_three _ _ _) ?_
    have h1 : |(p : ℝ) * Real.log (k : ℝ)| = (p : ℝ) * Real.log (k : ℝ) := by
      rw [abs_of_nonneg (by positivity)]
    have h2 : |(k : ℝ) * Real.log 2| = (k : ℝ) * Real.log 2 := by
      rw [abs_of_nonneg (by positivity)]
    rw [h1, h2]
    have h3 : (p : ℝ) * Real.log (k : ℝ) ≤ (p : ℝ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hlogkle (by positivity)
    linarith
  have hlogtotal : Real.log (1 + 2 * R * L / ε) ≤
      Real.log 2 + |Real.log (2 / ε₀)| + (p : ℝ) * (k : ℝ) + (k : ℝ) * Real.log 2 := by
    linarith [hmono, hlog2, hmaxle, habs]
  have hlognn : 0 ≤ Real.log (1 + 2 * R * L / ε) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ 2 * R * L / ε := by positivity
    linarith
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hk1]
  have hlog2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc (M : ℝ) * Real.log (1 + 2 * R * L / ε)
      ≤ (k : ℝ) * Real.log (1 + 2 * R * L / ε) := mul_le_mul_of_nonneg_right hMk' hlognn
    _ ≤ (k : ℝ) * (Real.log 2 + |Real.log (2 / ε₀)| + (p : ℝ) * (k : ℝ) +
          (k : ℝ) * Real.log 2) := mul_le_mul_of_nonneg_left hlogtotal hkpos.le
    _ ≤ (2 * Real.log 2 + |Real.log (2 / ε₀)| + (p : ℝ) + 1) * (k : ℝ) ^ 2 := by
        nlinarith [hkk, hkpos, hlog2pos, abs_nonneg (Real.log (2 / ε₀)), hk1]

end OrbitNet

end

end GaloisForLFunctions.HTGeometry
