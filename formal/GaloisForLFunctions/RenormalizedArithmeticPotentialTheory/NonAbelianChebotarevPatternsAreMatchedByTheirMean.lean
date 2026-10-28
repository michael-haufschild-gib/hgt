import GaloisForLFunctions.ArtinMertens.TheFrobeniusDensityTheoremInMertensForm
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheMatchingCoefficientIsTheLogarithmicDensity

/-!
# Non-abelian Chebotarev sign patterns are matched by their mean

Let `G` be a Galois group of a number field `L` over `ℚ`, `Frob_p` a choice of Frobenius elements at
the primes `p ∤ disc L`, and `f : G → {±1}` division-constant (`f(h) = f(g)` when `⟨h⟩` is conjugate
to `⟨g⟩`). The **Chebotarev pattern** `g(p) = f(Frob_p)` (and `g = 1` at ramified primes) has
logarithmic mean `⟨f, 1⟩ = |G|⁻¹ Σ_σ f(σ)` (`tendsto_chebotarevPattern_div_log`), so its gauge
`ε_g` has polar matching coefficient `κ = ⟨f, 1⟩`
(`tendsto_gaugeMertensSum_chebotarevPattern_div_log`) and obeys the soft law
`|P_N(ε_g x) − ⟨f, 1⟩ ℓ(x)²| ≤ (η log N + C_η) · mass` (`gaugeForm_chebotarevPattern_soft`).

The input is the Frobenius density theorem in Mertens form (`ArtinMertens`); the ramified primes
divide `disc L ≠ 0` and contribute a bounded amount.
-/

noncomputable section

open Finset Filter Topology NumberField
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArtinMertens

variable {L : Type*} [Field L] [NumberField L] {G : Type*} [Group G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G ℚ L]

variable (L) in
/-- The **Chebotarev pattern** of `f`: `g(p) = f(Frob_p)` at primes `p ∤ disc L`, `1` elsewhere. -/
def chebotarevPattern (frob : ℕ → G) (f : G → ℝ) (t : ℕ) : ℝ :=
  if t.Prime ∧ ¬ (t : ℤ) ∣ discr L then f (frob t) else 1

/-- The pattern's prime sum splits into the Frobenius–Mertens sum and the ramified primes. -/
theorem sum_chebotarevPattern_eq (frob : ℕ → G) (f : G → ℝ) (y : ℕ) :
    ∑ t ∈ Icc 1 y, (if t.Prime then chebotarevPattern L frob f t * Real.log t / t else 0) =
      frobMertens L frob f y + ∑ p ∈ ((Icc 1 y).filter Nat.Prime).filter
        (fun p : ℕ => (p : ℤ) ∣ discr L), Real.log p / p := by
  rw [← sum_filter, ← sum_filter_add_sum_filter_not _ (fun p : ℕ => (p : ℤ) ∣ discr L), add_comm,
    frobMertens]
  congr 1
  · refine sum_congr rfl fun p hp => ?_
    simp only [mem_filter] at hp
    rw [chebotarevPattern, if_pos ⟨hp.1.2, hp.2⟩, mul_div_assoc]
  · refine sum_congr rfl fun p hp => ?_
    simp only [mem_filter] at hp
    rw [chebotarevPattern, if_neg fun h => h.2 hp.2, one_mul]

variable (L) in
/-- The ramified primes divide `disc L ≠ 0`, so their sum is bounded. -/
theorem ramifiedLogSum_le (y : ℕ) :
    ∑ p ∈ ((Icc 1 y).filter Nat.Prime).filter (fun p : ℕ => (p : ℤ) ∣ discr L),
        Real.log p / p ≤
      ∑ p ∈ ((Icc 1 (discr L).natAbs).filter Nat.Prime).filter (fun p : ℕ => (p : ℤ) ∣ discr L),
        Real.log p / p := by
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ =>
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  simp only [mem_filter, mem_Icc] at hp ⊢
  refine ⟨⟨⟨hp.1.1.1, ?_⟩, hp.1.2⟩, hp.2⟩
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) (Int.natCast_dvd.mp hp.2)

/-- **The Chebotarev pattern has logarithmic mean `⟨f, 1⟩`**:
`Σ_{p ≤ y} g(p) log p/p ∼ ⟨f, 1⟩ log y` for every division-constant `f`. -/
theorem tendsto_chebotarevPattern_div_log {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob)
    {f : G → ℝ} (hf : IsDivisionConstant f) :
    Tendsto (fun y : ℕ => (∑ t ∈ Icc 1 y,
      (if t.Prime then chebotarevPattern L frob f t * Real.log t / t else 0)) / Real.log y)
        atTop (𝓝 (classMean f)) := by
  have hlog : Tendsto (fun y : ℕ => Real.log y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun y : ℕ => (∑ p ∈ ((Icc 1 y).filter Nat.Prime).filter
      (fun p : ℕ => (p : ℤ) ∣ discr L), Real.log p / p) / Real.log y) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ ((tendsto_const_nhds (x := ∑ p ∈ ((Icc 1 (discr L).natAbs).filter
      Nat.Prime).filter (fun p : ℕ => (p : ℤ) ∣ discr L), Real.log p / p)).div_atTop hlog)
    · filter_upwards [hlog.eventually_ge_atTop 0] with y hy
      exact div_nonneg (sum_nonneg fun p _ =>
        div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)) hy
    · filter_upwards [hlog.eventually_ge_atTop 0] with y hy
      exact div_le_div_of_nonneg_right (ramifiedLogSum_le L y) hy
  have h := (tendsto_frobMertens_div_log hfrob hf).add hR
  rw [add_zero] at h
  refine h.congr fun y => ?_
  rw [sum_chebotarevPattern_eq, add_div]

/-- A sign-valued `f` gives a sign pattern. -/
theorem chebotarevPattern_mul_self (frob : ℕ → G) {f : G → ℝ} (hf : ∀ σ, f σ * f σ = 1)
    (t : ℕ) : chebotarevPattern L frob f t * chebotarevPattern L frob f t = 1 := by
  unfold chebotarevPattern
  split_ifs
  · exact hf _
  · exact one_mul 1

/-- **Non-abelian Chebotarev patterns are matched by their mean**: `A_{ε_g}(y)/log y → ⟨f, 1⟩`. -/
theorem tendsto_gaugeMertensSum_chebotarevPattern_div_log {frob : ℕ → G}
    (hfrob : IsFrobeniusChoice L frob) {f : G → ℝ} (hf : ∀ σ, f σ * f σ = 1)
    (hfd : IsDivisionConstant f) :
    Tendsto (fun y : ℕ => gaugeMertensSum (primeSignGauge (chebotarevPattern L frob f)) y /
      Real.log y) atTop (𝓝 (classMean f)) :=
  tendsto_primeSignGauge_div_log (chebotarevPattern_mul_self frob hf)
    (tendsto_chebotarevPattern_div_log hfrob hfd)

/-- **The soft law for Chebotarev patterns**: for every `η > 0` there is `C` with
`|P_N(ε_g x) − ⟨f, 1⟩ ℓ(x)²| ≤ (η log N + C) Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}` on step
profiles. -/
theorem gaugeForm_chebotarevPattern_soft {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob)
    {f : G → ℝ} (hf : ∀ σ, f σ * f σ = 1) (hfd : IsDivisionConstant f) :
    ∀ η > 0, ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) →
      (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (fun n => primeSignGauge (chebotarevPattern L frob f) n *
          stepProfile c M n) - classMean f * polarFunctional N (stepProfile c M) ^ 2| ≤
        (η * Real.log N + C) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) :=
  gaugeForm_primeSignGauge_soft (chebotarevPattern_mul_self frob hf)
    (tendsto_chebotarevPattern_div_log hfrob hfd)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
