import GaloisForLFunctions.HTGeometry.GaussianLatticeTheta
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheBaseDoesNotExtend

/-!
# The slope of a lattice count is its rank

A full lattice `L = B ℤ^ι` in Euclidean space of rank `r = |ι|`, with its metric scaled by `e^{−d}`,
is an Arakelov bundle of rank `r` over `Spec ℤ` twisted by degree `d`. Its section count is

    h⁰(L, d) = log θ_L(e^{−2d}),      θ_L(t) = Σ_{k ∈ ℤ^ι} e^{−π t ‖B k‖²}.

* **Poisson Riemann–Roch** (`latticeH0_riemannRoch`):
  `h⁰(L, d) − h⁰(L*, −d) = r d + log(1 / covol L)`, the dual lattice being the inverse adjoint.
  The Euler characteristic is affine in the degree with slope the rank.
* **Slope law** (`latticeH0_slope`). Poisson summation and monotonicity of the dual count give
  Banaszczyk's inequality: for `d' ≤ d`,

      0 ≤ h⁰(L, d) − h⁰(L, d') ≤ r (d − d').

  In particular `h⁰(L, d) ≤ h⁰(L, 0) + r · max(d, 0)`.
* **Rank is the asymptotic slope** (`tendsto_latticeH0_atBot`, `tendsto_latticeH0_sub_atTop`):
  `h⁰(L, d) → 0` as `d → −∞` and `h⁰(L, d) − (r d + log(1/covol L)) → 0` as `d → +∞`.
* **Rank law** (`not_riemannInequality_of_bounded_rank`). On every polar surface, a section count
  `h(x) = h⁰(L(x), d(x))` built from lattices of one fixed rank with `h⁰(L(x), 0)` bounded and a
  degree `|d(x)| ≤ α + β |x · A|` violates the Riemann inequality: it grows at most linearly along
  the ample ray, while Hilbert–Samuel asks for `n²`. A surface `h⁰` needs section lattices whose
  rank grows with the class.
-/

noncomputable section

open Real Filter Topology

namespace GaloisForLFunctions.LatticeSectionTheory

open HTGeometry.IntegerLatticePoisson ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "Z" => ι → ℤ

omit [Fintype ι] in
theorem euclideanIntegerPoint_zero : euclideanIntegerPoint (0 : Z) = (0 : E) := by
  ext i; simp [euclideanIntegerPoint, integerPoint]

omit [Fintype ι] in
theorem euclideanIntegerPoint_ne_zero {k : Z} (hk : k ≠ 0) : euclideanIntegerPoint k ≠ (0 : E) := by
  intro h
  apply hk
  funext i
  have := congrArg (fun v : E => v i) h
  simpa [euclideanIntegerPoint, integerPoint] using this

/-- The `k`-th term of the lattice count at parameter `t`. -/
def latticeTerm (B : E ≃L[ℝ] E) (t : ℝ) (k : Z) : ℝ :=
  Real.exp (-(π * t) * ‖B (euclideanIntegerPoint k)‖ ^ 2)

theorem latticeTheta_eq_tsum (B : E ≃L[ℝ] E) (t : ℝ) :
    latticeTheta B t = ∑' k : Z, latticeTerm B t k := rfl

theorem summable_latticeTerm (B : E ≃L[ℝ] E) {t : ℝ} (ht : 0 < t) :
    Summable (latticeTerm B t) :=
  summable_gaussianLatticeSum B (mul_pos Real.pi_pos ht)

theorem latticeTerm_zero (B : E ≃L[ℝ] E) (t : ℝ) : latticeTerm B t 0 = 1 := by
  simp [latticeTerm, euclideanIntegerPoint_zero]

/-- The zero vector is a section: `θ_L(t) ≥ 1`. -/
theorem one_le_latticeTheta (B : E ≃L[ℝ] E) {t : ℝ} (ht : 0 < t) : 1 ≤ latticeTheta B t := by
  have := (summable_latticeTerm B ht).le_tsum 0 (fun k _ => (Real.exp_pos _).le)
  rwa [latticeTerm_zero] at this

theorem latticeTheta_pos (B : E ≃L[ℝ] E) {t : ℝ} (ht : 0 < t) : 0 < latticeTheta B t :=
  lt_of_lt_of_le zero_lt_one (one_le_latticeTheta B ht)

/-- The lattice count decreases as the metric grows. -/
theorem latticeTheta_antitone (B : E ≃L[ℝ] E) {t t' : ℝ} (ht : 0 < t) (htt' : t ≤ t') :
    latticeTheta B t' ≤ latticeTheta B t := by
  rw [latticeTheta_eq_tsum, latticeTheta_eq_tsum]
  refine (summable_latticeTerm B (ht.trans_le htt')).tsum_le_tsum (fun k => ?_)
    (summable_latticeTerm B ht)
  simp only [latticeTerm, Real.exp_le_exp]
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 htt') Real.pi_pos.le)
    (sq_nonneg ‖B (euclideanIntegerPoint k)‖)]

/-- **The lattice `h⁰`** of `L = B ℤ^ι` at degree `d`. -/
def latticeH0 (B : E ≃L[ℝ] E) (d : ℝ) : ℝ := Real.log (latticeTheta B (Real.exp (-2 * d)))

theorem latticeH0_nonneg (B : E ≃L[ℝ] E) (d : ℝ) : 0 ≤ latticeH0 B d :=
  Real.log_nonneg (one_le_latticeTheta B (Real.exp_pos _))

theorem latticeH0_mono (B : E ≃L[ℝ] E) : Monotone (latticeH0 B) := by
  intro d d' h
  refine Real.log_le_log (latticeTheta_pos B (Real.exp_pos _)) ?_
  exact latticeTheta_antitone B (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith))

/-- The rank `r = |ι|` as a real number. -/
abbrev latticeRank (ι : Type*) [Fintype ι] : ℝ := (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ)

/-- **Poisson Riemann–Roch for lattice counts**:
`h⁰(L, d) − h⁰(L*, −d) = r d + log(1 / covol L)`. -/
theorem latticeH0_riemannRoch (B : E ≃L[ℝ] E) (d : ℝ) :
    latticeH0 B d - latticeH0 (inverseAdjointEquiv B) (-d) =
      latticeRank ι * d + Real.log (latticeScale B) := by
  have ht : 0 < Real.exp (-2 * d) := Real.exp_pos _
  have hinv := latticeTheta_inversion B ht
  have hpow : Real.exp (-2 * d) ^ (-(latticeRank ι / 2)) = Real.exp (latticeRank ι * d) := by
    rw [← Real.exp_mul]; congr 1; ring
  have hrec : 1 / Real.exp (-2 * d) = Real.exp (-2 * -d) := by
    rw [one_div, ← Real.exp_neg]; congr 1; ring
  rw [hpow, hrec] at hinv
  unfold latticeH0
  rw [hinv, Real.log_mul (mul_pos (latticeScale_pos B) (Real.exp_pos _)).ne'
      (latticeTheta_pos _ (Real.exp_pos _)).ne',
    Real.log_mul (latticeScale_pos B).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- **Slope law** (Banaszczyk). The slope of `d ↦ h⁰(L, d)` lies in `[0, r]`. -/
theorem latticeH0_slope (B : E ≃L[ℝ] E) {d d' : ℝ} (h : d' ≤ d) :
    0 ≤ latticeH0 B d - latticeH0 B d' ∧
      latticeH0 B d - latticeH0 B d' ≤ latticeRank ι * (d - d') := by
  refine ⟨sub_nonneg.mpr (latticeH0_mono B h), ?_⟩
  have h1 := latticeH0_riemannRoch B d
  have h2 := latticeH0_riemannRoch B d'
  have h3 := latticeH0_mono (inverseAdjointEquiv B) (show -d ≤ -d' by linarith)
  linarith

/-- The section count of a lattice grows at most like its rank times the positive degree. -/
theorem latticeH0_le (B : E ≃L[ℝ] E) (d : ℝ) :
    latticeH0 B d ≤ latticeH0 B 0 + latticeRank ι * max d 0 := by
  rcases le_total 0 d with hd | hd
  · rw [max_eq_left hd]; linarith [(latticeH0_slope B hd).2]
  · rw [max_eq_right hd, mul_zero, add_zero]; exact latticeH0_mono B hd

/-- The lattice count tends to `1` (only the zero vector survives) as the metric blows up. -/
theorem tendsto_latticeTheta_atTop (B : E ≃L[ℝ] E) :
    Tendsto (latticeTheta B) atTop (𝓝 1) := by
  classical
  have hlim : ∀ k : Z, Tendsto (fun t => latticeTerm B t k) atTop
      (𝓝 (if k = 0 then 1 else 0)) := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp only [latticeTerm_zero, if_true]; exact tendsto_const_nhds
    · rw [if_neg hk]
      have hpos : 0 < ‖B (euclideanIntegerPoint k)‖ ^ 2 := by
        have := B.injective.ne (euclideanIntegerPoint_ne_zero hk)
        rw [map_zero] at this
        exact pow_pos (norm_pos_iff.mpr this) 2
      unfold latticeTerm
      refine Real.tendsto_exp_atBot.comp ?_
      have : Tendsto (fun t : ℝ => t * (-(π * ‖B (euclideanIntegerPoint k)‖ ^ 2))) atTop atBot :=
        tendsto_id.atTop_mul_const_of_neg (by nlinarith [Real.pi_pos])
      refine this.congr fun t => ?_
      ring
  have hbound : ∀ᶠ t in atTop, ∀ k : Z, ‖latticeTerm B t k‖ ≤ latticeTerm B 1 k := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht k
    have h0 : 0 ≤ latticeTerm B t k := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg h0]
    simp only [latticeTerm, Real.exp_le_exp]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ht) Real.pi_pos.le)
      (sq_nonneg ‖B (euclideanIntegerPoint k)‖)]
  have := tendsto_tsum_of_dominated_convergence (summable_latticeTerm B one_pos) hlim hbound
  rwa [tsum_ite_eq] at this

/-- **No sections in very negative degree**: `h⁰(L, d) → 0` as `d → −∞`. -/
theorem tendsto_latticeH0_atBot (B : E ≃L[ℝ] E) : Tendsto (latticeH0 B) atBot (𝓝 0) := by
  have hexp : Tendsto (fun d : ℝ => Real.exp (-2 * d)) atBot atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    have : Tendsto (fun d : ℝ => d * (-2)) atBot atTop :=
      tendsto_id.atBot_mul_const_of_neg (by norm_num)
    exact this.congr fun d => by ring
  have := (Real.continuousAt_log one_ne_zero).tendsto.comp
    ((tendsto_latticeTheta_atTop B).comp hexp)
  rw [Real.log_one] at this
  exact this

/-- **The rank is the asymptotic slope**: `h⁰(L, d) − (r d + log(1/covol L)) → 0` as `d → ∞`. -/
theorem tendsto_latticeH0_sub_atTop (B : E ≃L[ℝ] E) :
    Tendsto (fun d => latticeH0 B d - (latticeRank ι * d + Real.log (latticeScale B))) atTop
      (𝓝 0) := by
  have h := (tendsto_latticeH0_atBot (inverseAdjointEquiv B)).comp tendsto_neg_atTop_atBot
  refine h.congr fun d => ?_
  have := latticeH0_riemannRoch B d
  simp only [Function.comp]
  linarith

/-! ### The rank law on polar surfaces -/

section RankLaw

variable {F : Type*} [AddCommGroup F] [Module ℝ F] (S : PolarSurface F)

/-- **Rank law.** A section count `h(x) = h⁰(L(x), d(x))` built from lattices of one fixed rank, with
`h⁰(L(x), 0) ≤ C` and `|d(x)| ≤ α + β |x · A|`, violates the Riemann inequality on every polar
surface: bounded rank means at most linear growth along the ample ray. -/
theorem not_riemannInequality_of_bounded_rank {κ : F} {χ₀ C α β : ℝ}
    (L : F → (E ≃L[ℝ] E)) (deg : F → ℝ)
    (hC : ∀ x, latticeH0 (L x) 0 ≤ C) (hdeg : ∀ x, |deg x| ≤ α + β * |S.pair x S.ample|) :
    ¬ RiemannInequality S κ χ₀ (fun x => latticeH0 (L x) (deg x)) := by
  refine not_riemannInequality_of_affine_bound S (α := C + latticeRank ι * α)
    (β := latticeRank ι * β) fun x => ?_
  have h1 := latticeH0_le (L x) (deg x)
  have hr : 0 ≤ latticeRank ι := Nat.cast_nonneg _
  have h2 : max (deg x) 0 ≤ α + β * |S.pair x S.ample| :=
    max_le ((le_abs_self _).trans (hdeg x)) ((abs_nonneg _).trans (hdeg x))
  have h3 := mul_le_mul_of_nonneg_left h2 hr
  linarith [hC x]

/-- **One lattice is never a surface `h⁰`.** For a fixed lattice and a degree that is a linear
function of the class, the lattice count violates the Riemann inequality on every polar surface. -/
theorem not_riemannInequality_latticeH0_linear {κ : F} {χ₀ : ℝ} (B : E ≃L[ℝ] E)
    (deg : F →ₗ[ℝ] ℝ) : ¬ RiemannInequality S κ χ₀ (fun x => latticeH0 B (deg x)) := by
  intro hRI
  -- along `nA` the count is at most affine in `n`, while Hilbert–Samuel asks for `n²`
  set a := deg S.ample
  set k := deg κ
  obtain ⟨n, hn1, hn2⟩ := ((hilbertSamuel_of_riemannInequality S hRI
    (by norm_num : (1 / 2 : ℝ) < 1)).and (eventually_affine_lt_quadratic
      (by norm_num : (0 : ℝ) < 1 / 2) (2 * latticeRank ι * |a|)
        (2 * latticeH0 B 0 + latticeRank ι * |k|))).exists
  have hr : 0 ≤ latticeRank ι := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : deg ((n : ℝ) • S.ample) = n * a := by rw [map_smul, smul_eq_mul]
  have e2 : deg (κ - (n : ℝ) • S.ample) = k - n * a := by rw [map_sub, e1]
  have b1 := latticeH0_le B (deg ((n : ℝ) • S.ample))
  have b2 := latticeH0_le B (deg (κ - (n : ℝ) • S.ample))
  rw [e1] at b1 hn1
  rw [e2] at b2 hn1
  have m1 : max (n * a) 0 ≤ n * |a| :=
    max_le (mul_le_mul_of_nonneg_left (le_abs_self a) hn0) (by positivity)
  have m2 : max (k - n * a) 0 ≤ |k| + n * |a| := by
    refine max_le ?_ (by positivity)
    have := neg_abs_le a
    nlinarith [le_abs_self k]
  have c1 := mul_le_mul_of_nonneg_left m1 hr
  have c2 := mul_le_mul_of_nonneg_left m2 hr
  nlinarith

end RankLaw

end GaloisForLFunctions.LatticeSectionTheory
