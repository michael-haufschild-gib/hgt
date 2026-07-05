/-
The full-support carrier small-ball bound: the anti-concentration of `∑_{n≤N} aₙ Xₙ` in the
completely multiplicative Steinhaus model, reduced to the four-phase caustic bound.

`inner_block_le`/`block_pi_le` bound the small-ball of `w + Σ_{p∈s} aₚ Xₚ` for a prime block `s` and a
CONSTANT shift `w`. Here the shift is a genuine random remainder: with the four dominant primes chosen
in `(N/2, N]`, the carrier splits (via `carrier_dominant_decomp`) as the four pure dominant terms plus
a remainder over integers divisible by none of the `pᵢ`; that remainder reads only complement
coordinates and is therefore an independent random shift. Marginalizing the model measure over the four
dominant coordinates leaves the inner four-phase integral bounded by `M` uniformly in the frozen value
of the remainder, and the complement integrates that constant against a probability measure — the same
`lmarginal`/`rescale4` machinery as the constant-shift block law, generalized to an arbitrary
coordinate-invariant background.
-/
import GaloisForLFunctions.RHTower.RouteBFullSupport
import GaloisForLFunctions.RHTower.RouteBBlockSplit

open Complex Finset MeasureTheory
open RHTower.SteinhausModel

namespace RHTower
namespace SteinhausModel

/-- **Generalized inner four-marginal bound.** For four distinct coordinates and an arbitrary
background `g` invariant under those four coordinates, the four-coordinate marginal of the small-ball
indicator `‖g x + Σᵢ bᵢ·unitPhase(x qᵢ)‖ ≤ t` is at most `(2π)⁻⁴ M`, whenever the four phases satisfy
the uniform four-phase bound `M` at every center. -/
theorem inner_block_le_general {ι : Type} [DecidableEq ι]
    (g : (ι → ℝ) → ℂ) (b1 b2 b3 b4 : ℂ) (t : ℝ)
    (q1 q2 q3 q4 : ι) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h14 : q1 ≠ q4)
    (h23 : q2 ≠ q3) (h24 : q2 ≠ q4) (h34 : q3 ≠ q4) (M : ENNReal)
    (hg1 : ∀ x v, g (Function.update x q1 v) = g x)
    (hg2 : ∀ x v, g (Function.update x q2 v) = g x)
    (hg3 : ∀ x v, g (Function.update x q3 v) = g x)
    (hg4 : ∀ x v, g (Function.update x q4 v) = g x)
    (hgm : Measurable g)
    (hM : ∀ V : ℂ,
      (∫⁻ θD in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θC in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θB in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θA in Set.Icc (0:ℝ) (2*Real.pi),
          {θ' : ℝ | ‖V + b1 * Complex.exp ((θD:ℂ)*Complex.I)
              + b2 * Complex.exp ((θC:ℂ)*Complex.I)
              + b3 * Complex.exp ((θB:ℂ)*Complex.I)
              + b4 * Complex.exp ((θ':ℂ)*Complex.I)‖ ≤ t}.indicator
            (fun _ => (1:ENNReal)) θA) ≤ M)
    (y : ι → ℝ) :
    (∫⋯∫⁻_{q1, q2, q3, q4},
        ({x : ι → ℝ | ‖g x + b1 * unitPhase (x q1) + b2 * unitPhase (x q2)
            + b3 * unitPhase (x q3) + b4 * unitPhase (x q4)‖ ≤ t}.indicator
          (fun _ => (1:ENNReal)))
        ∂(fun _ : ι => volume.restrict (Set.Icc (0:ℝ) 1))) y
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
  set μ : ι → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1) with hμ
  set V : ℂ := g y with hV
  set Gfun : ℝ → ℝ → ℝ → ℝ → ENNReal := fun θ1 θ2 θ3 θ4 =>
    {z : ℂ | ‖z‖ ≤ t}.indicator (fun _ => (1:ENNReal))
      (V + b1 * Complex.exp ((θ1:ℂ)*Complex.I)
        + b2 * Complex.exp ((θ2:ℂ)*Complex.I)
        + b3 * Complex.exp ((θ3:ℂ)*Complex.I)
        + b4 * Complex.exp ((θ4:ℂ)*Complex.I)) with hGfun
  have hSm : MeasurableSet {z : ℂ | ‖z‖ ≤ t} :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have hFm : Measurable (fun x : ι → ℝ => g x + b1 * unitPhase (x q1) + b2 * unitPhase (x q2)
      + b3 * unitPhase (x q3) + b4 * unitPhase (x q4)) := by
    have hp : ∀ q : ι, Measurable (fun x : ι → ℝ => unitPhase (x q)) := by
      intro q; unfold unitPhase; fun_prop
    exact (((hgm.add (measurable_const.mul (hp q1))).add
      (measurable_const.mul (hp q2))).add (measurable_const.mul (hp q3))).add
      (measurable_const.mul (hp q4))
  have hEm : MeasurableSet {x : ι → ℝ | ‖g x + b1 * unitPhase (x q1) + b2 * unitPhase (x q2)
      + b3 * unitPhase (x q3) + b4 * unitPhase (x q4)‖ ≤ t} :=
    hFm.norm measurableSet_Iic
  have hf : Measurable ({x : ι → ℝ | ‖g x + b1 * unitPhase (x q1) + b2 * unitPhase (x q2)
      + b3 * unitPhase (x q3) + b4 * unitPhase (x q4)‖ ≤ t}.indicator (fun _ => (1:ENNReal))) :=
    measurable_const.indicator hEm
  rw [peel4 μ _ hf q1 q2 q3 q4 h12 h13 h14 h23 h24 h34 y]
  have hpt : ∀ x1 x2 x3 x4 : ℝ,
      ({x : ι → ℝ | ‖g x + b1 * unitPhase (x q1) + b2 * unitPhase (x q2)
          + b3 * unitPhase (x q3) + b4 * unitPhase (x q4)‖ ≤ t}.indicator (fun _ => (1:ENNReal)))
        (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4)
      = Gfun (2*Real.pi*x1) (2*Real.pi*x2) (2*Real.pi*x3) (2*Real.pi*x4) := by
    intro x1 x2 x3 x4
    have hgval : g (Function.update (Function.update (Function.update
        (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) = g y := by
      rw [hg4, hg3, hg2, hg1]
    have hval : g (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4)
        + b1 * unitPhase ((Function.update (Function.update (Function.update
            (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q1)
        + b2 * unitPhase ((Function.update (Function.update (Function.update
            (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q2)
        + b3 * unitPhase ((Function.update (Function.update (Function.update
            (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q3)
        + b4 * unitPhase ((Function.update (Function.update (Function.update
            (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q4)
        = V + b1 * Complex.exp (((2*Real.pi*x1:ℝ):ℂ)*Complex.I)
            + b2 * Complex.exp (((2*Real.pi*x2:ℝ):ℂ)*Complex.I)
            + b3 * Complex.exp (((2*Real.pi*x3:ℝ):ℂ)*Complex.I)
            + b4 * Complex.exp (((2*Real.pi*x4:ℝ):ℂ)*Complex.I) := by
      rw [hgval, hV]
      have e1 : (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q1 = x1 := by
        simp [Function.update_of_ne, h12, h13, h14]
      have e2 : (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q2 = x2 := by
        simp [Function.update_of_ne, h23, h24]
      have e3 : (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q3 = x3 := by
        simp [Function.update_of_ne, h34]
      have e4 : (Function.update (Function.update (Function.update
          (Function.update y q1 x1) q2 x2) q3 x3) q4 x4) q4 = x4 := by
        simp [Function.update_self]
      rw [e1, e2, e3, e4]
      have hu : ∀ x : ℝ, unitPhase x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
        intro x; unfold unitPhase; congr 1; push_cast; ring
      rw [hu x1, hu x2, hu x3, hu x4]
    simp only [hGfun, Set.indicator_apply, Set.mem_setOf_eq, hval]
  simp only [hμ]
  simp_rw [hpt]
  rw [rescale4 Gfun (by
    simp only [hGfun]
    exact (measurable_const.indicator hSm).comp (by fun_prop))]
  refine mul_le_mul_right ?_ _
  refine le_trans (le_of_eq ?_) (hM V)
  simp only [hGfun, Set.indicator_apply, Set.mem_setOf_eq]

/-- **Generalized finite-product block bound.** Over a finite product of uniform phases, the small-ball
probability of `g x + Σᵢ bᵢ·unitPhase(x qᵢ)` with `g` invariant under the four block coordinates is at
most `(2π)⁻⁴ M`. The four dominant coordinates give the four-phase bound `M` uniformly; the rest
integrate against a probability measure. -/
theorem block_pi_le_general {ι : Type} [DecidableEq ι] [Fintype ι]
    (g : (ι → ℝ) → ℂ) (b1 b2 b3 b4 : ℂ) (t : ℝ)
    (q1 q2 q3 q4 : ι) (h12 : q1 ≠ q2) (h13 : q1 ≠ q3) (h14 : q1 ≠ q4)
    (h23 : q2 ≠ q3) (h24 : q2 ≠ q4) (h34 : q3 ≠ q4) (M : ENNReal)
    (hg1 : ∀ x v, g (Function.update x q1 v) = g x)
    (hg2 : ∀ x v, g (Function.update x q2 v) = g x)
    (hg3 : ∀ x v, g (Function.update x q3 v) = g x)
    (hg4 : ∀ x v, g (Function.update x q4 v) = g x)
    (hgm : Measurable g)
    (hM : ∀ V : ℂ,
      (∫⁻ θD in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θC in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θB in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θA in Set.Icc (0:ℝ) (2*Real.pi),
          {θ' : ℝ | ‖V + b1 * Complex.exp ((θD:ℂ)*Complex.I)
              + b2 * Complex.exp ((θC:ℂ)*Complex.I)
              + b3 * Complex.exp ((θB:ℂ)*Complex.I)
              + b4 * Complex.exp ((θ':ℂ)*Complex.I)‖ ≤ t}.indicator
            (fun _ => (1:ENNReal)) θA) ≤ M) :
    (Measure.pi (fun _ : ι => volume.restrict (Set.Icc (0:ℝ) 1)))
        {x : ι → ℝ | ‖g x + b1 * unitPhase (x q1) + b2 * unitPhase (x q2)
            + b3 * unitPhase (x q3) + b4 * unitPhase (x q4)‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
  haveI : ∀ i : ι, IsProbabilityMeasure ((fun _ : ι => volume.restrict (Set.Icc (0:ℝ) 1)) i) :=
    fun _ => ⟨by simp⟩
  set μ : ι → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1) with hμ
  set E := {x : ι → ℝ | ‖g x + b1 * unitPhase (x q1) + b2 * unitPhase (x q2)
      + b3 * unitPhase (x q3) + b4 * unitPhase (x q4)‖ ≤ t} with hE
  have hFm : Measurable (fun x : ι → ℝ => g x + b1 * unitPhase (x q1) + b2 * unitPhase (x q2)
      + b3 * unitPhase (x q3) + b4 * unitPhase (x q4)) := by
    have hp : ∀ q : ι, Measurable (fun x : ι → ℝ => unitPhase (x q)) := by
      intro q; unfold unitPhase; fun_prop
    exact (((hgm.add (measurable_const.mul (hp q1))).add
      (measurable_const.mul (hp q2))).add (measurable_const.mul (hp q3))).add
      (measurable_const.mul (hp q4))
  have hEm : MeasurableSet E := hFm.norm measurableSet_Iic
  have hfm : Measurable (E.indicator (fun _ => (1:ENNReal))) := measurable_const.indicator hEm
  have hpiE : (Measure.pi μ) E = ∫⁻ x, E.indicator (fun _ => (1:ENNReal)) x ∂(Measure.pi μ) := by
    rw [lintegral_indicator hEm, setLIntegral_one]
  rw [hpiE, lintegral_eq_lmarginal_univ (μ := μ) (fun _ => (0:ℝ))]
  rw [show (Finset.univ : Finset ι)
        = (Finset.univ \ {q1, q2, q3, q4}) ∪ {q1, q2, q3, q4} from
      (Finset.sdiff_union_of_subset (Finset.subset_univ _)).symm]
  rw [lmarginal_union μ _ hfm Finset.sdiff_disjoint]
  have hbound : (fun z => (∫⋯∫⁻_{q1, q2, q3, q4}, E.indicator (fun _ => (1:ENNReal)) ∂μ) z)
      ≤ fun _ => ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
    intro z
    exact inner_block_le_general g b1 b2 b3 b4 t q1 q2 q3 q4 h12 h13 h14 h23 h24 h34 M
      hg1 hg2 hg3 hg4 hgm hM z
  refine le_trans (lmarginal_mono hbound _) (le_of_eq ?_)
  rw [lmarginal]
  simp only [lintegral_const]
  rw [measure_univ, mul_one]

/-- Extend a finite-coordinate point to a full phase configuration by zero outside `T`. -/
noncomputable def extendT (T : Finset ℕ) (x : ↥T → ℝ) : Omega :=
  fun q => if h : q ∈ T then x ⟨q, h⟩ else 0

theorem restrict_extendT (T : Finset ℕ) (x : ↥T → ℝ) : T.restrict (extendT T x) = x := by
  funext i
  simp only [Finset.restrict, extendT, i.2, dif_pos]

theorem measurable_extendT (T : Finset ℕ) : Measurable (extendT T) := by
  apply measurable_pi_iff.mpr
  intro q
  by_cases h : q ∈ T
  · simp only [extendT, h, dif_pos]; exact measurable_pi_apply _
  · simp only [extendT, h, dif_neg, not_false_iff]; exact measurable_const

/-- The prime factors of any `n ∈ [1,N]` lie in the prime set of `[1,N]`. -/
theorem primeFactors_subset_primesIcc {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    n.primeFactors ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hqP, hqd, hn0⟩ := hq
  rw [Finset.mem_filter, Finset.mem_Icc]
  rw [Finset.mem_Icc] at hn
  exact ⟨⟨hqP.one_lt.le, le_trans (Nat.le_of_dvd (by omega) hqd) hn.2⟩, hqP⟩

/-- Reducing a `T`-restriction-invariant small-ball event to the finite product measure over `↥T`. -/
theorem steinhausMeasure_eq_pi_restrict {T : Finset ℕ} {F : Set (↥T → ℝ)} (hF : MeasurableSet F) :
    steinhausMeasure (T.restrict ⁻¹' F)
      = (Measure.pi fun _ : ↥T => volume.restrict (Set.Icc (0:ℝ) 1)) F := by
  rw [steinhausMeasure, ← Measure.map_apply (Finset.measurable_restrict T) hF,
    MeasureTheory.Measure.infinitePi_map_restrict]

/-- **Full-support carrier small-ball from the four-phase bound.** With four distinct primes
`p₁,…,p₄ ∈ (N/2, N]` (so each is its own only multiple in `[1,N]`), the completely multiplicative
carrier `∑_{n≤N} aₙ Xₙ` has Steinhaus small-ball probability at most `(2π)⁻⁴ M`, whenever the four
dominant phases `aₚᵢ` satisfy the uniform four-phase bound `M`. The carrier splits into the four pure
dominant terms plus an independent complement remainder, and the marginal over the four dominant
coordinates is bounded uniformly in that remainder. -/
theorem fullCarrier_smallball_of_fourPhase {N : ℕ} (a : ℕ → ℝ) {t : ℝ} {M : ENNReal}
    {p1 p2 p3 p4 : ℕ}
    (hp1P : p1.Prime) (hp2P : p2.Prime) (hp3P : p3.Prime) (hp4P : p4.Prime)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hM : ∀ V : ℂ,
      (∫⁻ θD in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θC in Set.Icc (0:ℝ) (2*Real.pi),
        ∫⁻ θB in Set.Icc (0:ℝ) (2*Real.pi), ∫⁻ θA in Set.Icc (0:ℝ) (2*Real.pi),
          {θ' : ℝ | ‖V + (a p1:ℂ) * Complex.exp ((θD:ℂ)*Complex.I)
              + (a p2:ℂ) * Complex.exp ((θC:ℂ)*Complex.I)
              + (a p3:ℂ) * Complex.exp ((θB:ℂ)*Complex.I)
              + (a p4:ℂ) * Complex.exp ((θ':ℂ)*Complex.I)‖ ≤ t}.indicator
            (fun _ => (1:ENNReal)) θA) ≤ M) :
    steinhausMeasure {ω : Omega | ‖∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4 * M := by
  classical
  set T : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime with hT
  have hp1T : p1 ∈ T := Finset.mem_filter.mpr ⟨hp1I, hp1P⟩
  have hp2T : p2 ∈ T := Finset.mem_filter.mpr ⟨hp2I, hp2P⟩
  have hp3T : p3 ∈ T := Finset.mem_filter.mpr ⟨hp3I, hp3P⟩
  have hp4T : p4 ∈ T := Finset.mem_filter.mpr ⟨hp4I, hp4P⟩
  set q1 : ↥T := ⟨p1, hp1T⟩ with hq1
  set q2 : ↥T := ⟨p2, hp2T⟩ with hq2
  set q3 : ↥T := ⟨p3, hp3T⟩ with hq3
  set q4 : ↥T := ⟨p4, hp4T⟩ with hq4
  have hq12 : q1 ≠ q2 := fun h => h12 (Subtype.ext_iff.mp h)
  have hq13 : q1 ≠ q3 := fun h => h13 (Subtype.ext_iff.mp h)
  have hq14 : q1 ≠ q4 := fun h => h14 (Subtype.ext_iff.mp h)
  have hq23 : q2 ≠ q3 := fun h => h23 (Subtype.ext_iff.mp h)
  have hq24 : q2 ≠ q4 := fun h => h24 (Subtype.ext_iff.mp h)
  have hq34 : q3 ≠ q4 := fun h => h34 (Subtype.ext_iff.mp h)
  set restFilter : Finset ℕ := (Finset.Icc 1 N).filter (fun n => ¬ (p1 ∣ n ∨ p2 ∣ n ∨ p3 ∣ n ∨ p4 ∣ n))
    with hrestFilter
  set g : (↥T → ℝ) → ℂ := fun x => ∑ n ∈ restFilter, (a n : ℂ) * X n (extendT T x) with hg
  -- `X n (extendT T x)` for `n ≤ N` depends only on the `T`-coordinates present in `x`
  -- Key evaluation: on prime factors of `n ∈ [1,N]`, `extendT T x` reads `x`.
  have hExtEval : ∀ (n : ℕ), n ∈ Finset.Icc 1 N → ∀ x : ↥T → ℝ,
      X n (extendT T x) = X n (extendT T x) := fun _ _ _ => rfl
  -- The background `g` is invariant under the four dominant coordinates.
  have hginv : ∀ (i : ℕ) (hiT : i ∈ T)
      (hi : ∀ n ∈ restFilter, i ∉ n.primeFactors),
      ∀ x v, g (Function.update x ⟨i, hiT⟩ v) = g x := by
    intro i hiT hi x v
    rw [hg]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply X_congr_of_eqOn_primeFactors
    intro q hq
    have hqT : q ∈ T := primeFactors_subset_primesIcc (Finset.mem_filter.mp hn).1 hq
    have hqne : q ≠ i := by
      rintro rfl; exact hi n hn hq
    simp only [extendT, hqT, dif_pos]
    exact Function.update_of_ne (by exact fun h => hqne (Subtype.ext_iff.mp h)) _ _
  -- membership: each pᵢ is absent from the prime factors of every remainder index
  have hnotp : ∀ (p : ℕ) (hp : p.Prime), (∀ n ∈ restFilter, ¬ p ∣ n) →
      ∀ n ∈ restFilter, p ∉ n.primeFactors := by
    intro p hp hnd n hn
    exact not_mem_primeFactors_of_not_dvd (hnd n hn)
  have hrestNoDvd : ∀ n ∈ restFilter, ¬ p1 ∣ n ∧ ¬ p2 ∣ n ∧ ¬ p3 ∣ n ∧ ¬ p4 ∣ n := by
    intro n hn
    have := (Finset.mem_filter.mp hn).2
    rw [not_or, not_or, not_or] at this
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  have hg1 : ∀ x v, g (Function.update x q1 v) = g x :=
    hginv p1 hp1T (hnotp p1 hp1P (fun n hn => (hrestNoDvd n hn).1))
  have hg2 : ∀ x v, g (Function.update x q2 v) = g x :=
    hginv p2 hp2T (hnotp p2 hp2P (fun n hn => (hrestNoDvd n hn).2.1))
  have hg3 : ∀ x v, g (Function.update x q3 v) = g x :=
    hginv p3 hp3T (hnotp p3 hp3P (fun n hn => (hrestNoDvd n hn).2.2.1))
  have hg4 : ∀ x v, g (Function.update x q4 v) = g x :=
    hginv p4 hp4T (hnotp p4 hp4P (fun n hn => (hrestNoDvd n hn).2.2.2))
  have hgm : Measurable g := by
    rw [hg]
    apply Finset.measurable_sum
    intro n _
    exact (measurable_const.mul ((measurable_X n).comp (measurable_extendT T)))
  -- the carrier equals `g(restrict ω) + Σᵢ aₚᵢ·unitPhase((restrict ω) qᵢ)` pointwise
  have hunit_of_prime : ∀ (p : ℕ) (hp : p.Prime) (η : Omega),
      X p η = unitPhase (η p) := by
    intro p hp η
    rw [X_prime hp η]; unfold unitPhase; ring_nf
  have hcarrier : ∀ ω : Omega, ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω
      = g (T.restrict ω) + (a p1 : ℂ) * unitPhase ((T.restrict ω) q1)
          + (a p2 : ℂ) * unitPhase ((T.restrict ω) q2)
          + (a p3 : ℂ) * unitPhase ((T.restrict ω) q3)
          + (a p4 : ℂ) * unitPhase ((T.restrict ω) q4) := by
    intro ω
    have hXeq : ∀ n ∈ Finset.Icc 1 N, X n ω = X n (extendT T (T.restrict ω)) := by
      intro n hn
      apply X_congr_of_eqOn_primeFactors
      intro q hq
      have hqT : q ∈ T := primeFactors_subset_primesIcc hn hq
      simp only [extendT, hqT, dif_pos, Finset.restrict]
    have hstep1 : ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω
        = ∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n (extendT T (T.restrict ω)) := by
      apply Finset.sum_congr rfl
      intro n hn; rw [hXeq n hn]
    rw [hstep1,
      carrier_dominant_decomp (fun n => (a n : ℂ) * X n (extendT T (T.restrict ω)))
        hp1I hp2I hp3I hp4I hN1 hN2 hN3 hN4 h12 h13 h14 h23 h24 h34]
    have hpi : ∀ (p : ℕ) (hp : p.Prime) (hpT : p ∈ T),
        X p (extendT T (T.restrict ω)) = unitPhase ((T.restrict ω) ⟨p, hpT⟩) := by
      intro p hp hpT
      rw [hunit_of_prime p hp]
      congr 1
      simp only [extendT, hpT, dif_pos]
    rw [hpi p1 hp1P hp1T, hpi p2 hp2P hp2T, hpi p3 hp3P hp3T, hpi p4 hp4P hp4T]
    rw [hg]
    ring
  set F : Set (↥T → ℝ) := {x : ↥T → ℝ | ‖g x + (a p1 : ℂ) * unitPhase (x q1)
      + (a p2 : ℂ) * unitPhase (x q2) + (a p3 : ℂ) * unitPhase (x q3)
      + (a p4 : ℂ) * unitPhase (x q4)‖ ≤ t} with hF
  have hevent : {ω : Omega | ‖∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω‖ ≤ t}
      = T.restrict ⁻¹' F := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hF, hcarrier ω]
  have hFm2 : Measurable (fun x : ↥T → ℝ => g x + (a p1 : ℂ) * unitPhase (x q1)
      + (a p2 : ℂ) * unitPhase (x q2) + (a p3 : ℂ) * unitPhase (x q3)
      + (a p4 : ℂ) * unitPhase (x q4)) := by
    have hp : ∀ q : ↥T, Measurable (fun x : ↥T → ℝ => unitPhase (x q)) := by
      intro q; unfold unitPhase; fun_prop
    exact (((hgm.add (measurable_const.mul (hp q1))).add
      (measurable_const.mul (hp q2))).add (measurable_const.mul (hp q3))).add
      (measurable_const.mul (hp q4))
  have hFmeas : MeasurableSet F := hFm2.norm measurableSet_Iic
  rw [hevent, steinhausMeasure_eq_pi_restrict hFmeas]
  exact block_pi_le_general g (a p1 : ℂ) (a p2 : ℂ) (a p3 : ℂ) (a p4 : ℂ) t
    q1 q2 q3 q4 hq12 hq13 hq14 hq23 hq24 hq34 M hg1 hg2 hg3 hg4 hgm hM

/-- **Full-support carrier caustic small-ball law.** For the full-support carrier `∑_{n≤N} aₙ Xₙ`
with four distinct dominant primes in `(N/2, N]` in strict caustic position, the Steinhaus small-ball
probability is at most `(2π)⁻⁴` times the explicit four-phase constant — the full-support analog of
`block_smallball_caustic`, with the composite terms handled by the dominant-block decomposition rather
than a prime-only support. -/
theorem fullCarrier_smallball_caustic {N : ℕ} (a : ℕ → ℝ) {t σ0 sstar : ℝ} {J : ℕ}
    {p1 p2 p3 p4 : ℕ}
    (hp1P : p1.Prime) (hp2P : p2.Prime) (hp3P : p3.Prime) (hp4P : p4.Prime)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hA : (a p4:ℂ) ≠ 0) (hB : (a p3:ℂ) ≠ 0) (hC : (a p2:ℂ) ≠ 0) (hD : (a p1:ℂ) ≠ 0)
    (hρB : ‖(a p3:ℂ)‖ < ‖(a p4:ℂ)‖) (hr0 : 0 < t)
    (hr2 : 2 * t ≤ ‖(a p4:ℂ)‖ - ‖(a p3:ℂ)‖) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖(a p4:ℂ)‖ + ‖(a p3:ℂ)‖) ^ 2 - (‖(a p4:ℂ)‖ - ‖(a p3:ℂ)‖) ^ 2) / 3)
    (hJ : ((‖(a p4:ℂ)‖ + ‖(a p3:ℂ)‖) ^ 2 - (‖(a p4:ℂ)‖ - ‖(a p3:ℂ)‖) ^ 2) / 3
        < 2 ^ J * σ0)
    (hHσ0 : 2 * (t * (2 * ‖(a p4:ℂ)‖ + t)
        / ((‖(a p4:ℂ)‖ - ‖(a p3:ℂ)‖) * ‖(a p3:ℂ)‖))
        ≤ σ0 * Sublevel.causticKappa ‖(a p4:ℂ)‖ ‖(a p3:ℂ)‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖(a p1:ℂ)‖) :
    steinhausMeasure {ω : Omega | ‖∑ n ∈ Finset.Icc 1 N, (a n : ℂ) * X n ω‖ ≤ t}
      ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
          * Sublevel.fourPhaseConst (a p4:ℂ) (a p3:ℂ) (a p2:ℂ) (a p1:ℂ) t σ0 sstar J :=
  fullCarrier_smallball_of_fourPhase a hp1P hp2P hp3P hp4P hp1I hp2I hp3I hp4I
    hN1 hN2 hN3 hN4 h12 h13 h14 h23 h24 h34
    (fun V => Sublevel.four_phase_nested_uniform (w := V) hA hB hC hD hρB hr0 hr2
      hσ0 hσ0G hJ hHσ0 hss hss2)

end SteinhausModel
end RHTower
