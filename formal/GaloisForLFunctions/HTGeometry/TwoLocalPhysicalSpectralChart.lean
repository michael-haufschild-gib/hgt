import GaloisForLFunctions.HTGeometry.HermitianLocalSpectralObserverLaw
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.ProjectiveRatioAffineEscape
import GaloisForLFunctions.HTGeometry.SortedEigenbranchAnalytic
import GaloisForLFunctions.HTGeometry.TwoLocalAnalyticAffineEscape

/-!
# A physical real chart for the two-local spectrum

The complex eigenbranch chart of the universal all-qubit two-local family
restricts to a real open ball of ordinary time-independent Hermitian
Hamiltonians.  On that same ball the labelled energies are real analytic,
remain simple, and every nonconstant affine spectral action escapes every
prescribed value.  This is the physical bridge needed by the projective
Diophantine recurrence theorem.
-/

open scoped BigOperators
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- The real numbered coefficient vector underlying a complex two-local
edge slice. -/
def twoLocalFinRealEdgeSlice
    (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n) (q : ℝ × ℝ) :
    Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ :=
  fun t =>
    let theta := (twoLocalParameterEquivFin n).symm t
    (p + q.1 • edgeShiftDirection i) theta +
      q.2 * (if theta = HypercubeTwoLocalParameter.transverse i then 1 else 0)

theorem realEmbed_twoLocalFinRealEdgeSlice
    (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n) (q : ℝ × ℝ) :
    realEmbed (twoLocalFinRealEdgeSlice p i q) =
      fun t => twoLocalEdgeSlice p i q ((twoLocalParameterEquivFin n).symm t) := by
  funext t
  by_cases ht : (twoLocalParameterEquivFin n).symm t =
      HypercubeTwoLocalParameter.transverse i
  · simp [realEmbed, twoLocalFinRealEdgeSlice, twoLocalEdgeSlice, ht]
  · simp [realEmbed, twoLocalFinRealEdgeSlice, twoLocalEdgeSlice, ht]

theorem continuous_twoLocalFinRealEdgeSlice
    (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n) :
    Continuous (twoLocalFinRealEdgeSlice p i) := by
  refine continuous_pi fun t => ?_
  simp only [twoLocalFinRealEdgeSlice]
  fun_prop

theorem twoLocalFinRealEdgeSlice_zero
    (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n) :
    twoLocalFinRealEdgeSlice p i (0, 0) =
      fun t => p ((twoLocalParameterEquivFin n).symm t) := by
  funext t
  simp [twoLocalFinRealEdgeSlice]

/-- **Physical two-local analytic chart with affine spectral escape.**
There is one real open connected ball of ordinary, time-independent,
all-qubit two-local Hamiltonians on which the labelled spectrum is simple
and real analytic.  Every nonconstant real linear action of those levels
escapes every prescribed constant inside that same physical ball. -/
theorem exists_twoLocalFinRealAnalyticChart_affineEscape (n : ℕ) :
    ∃ (U : Set (Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ))
      (p₀ : Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ)
      (energy : (Fin n → Bool) →
        (Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ) → ℝ),
      IsOpen U ∧ IsPreconnected U ∧ p₀ ∈ U ∧
      (∀ x, AnalyticOnNhd ℝ (energy x) U) ∧
      (∀ q ∈ U, Function.Injective fun x => energy x q) ∧
      (∀ c : (Fin n → Bool) → ℝ,
        (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
          ∃ q ∈ U, (∑ x, c x * energy x q) ≠ target) := by
  classical
  let M := hypercubeTwoLocalFinPolynomialMatrix n
  let embed : (HypercubeTwoLocalParameter n → ℂ) →
      (Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℂ) :=
    fun v t => v ((twoLocalParameterEquivFin n).symm t)
  obtain ⟨p, V, branch, htr, hinj, hgappos, hgapinj, hVopen, _hVconn, _hVne,
      hz₀V, hbranchA, hbranch0, hbranchInj, hbranchRoot⟩ :=
    exists_embeddedTwoLocalAnalyticChart M embed (fun _ => 0) (by
      intro p'
      rw [show (((0 : ℝ) : ℂ)) •
        (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 0 by simp, sub_zero]
      exact map_eval_embed_twoLocalFin fun theta => (p' theta : ℂ))
  let p₀ : Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ :=
    fun t => p ((twoLocalParameterEquivFin n).symm t)
  have hp₀V : realEmbed p₀ ∈ V := by
    change (fun t => ((p ((twoLocalParameterEquivFin n).symm t) : ℝ) : ℂ)) ∈ V
    simpa [embed] using hz₀V
  have hpreOpen : IsOpen (realEmbed ⁻¹' V) :=
    hVopen.preimage continuous_realEmbed
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp
    (hpreOpen.mem_nhds hp₀V)
  let U : Set (Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ) :=
    Metric.ball p₀ epsilon
  let energy : (Fin n → Bool) →
      (Fin (Fintype.card (HypercubeTwoLocalParameter n)) → ℝ) → ℝ :=
    fun x q => (branch x (realEmbed q)).re
  have hUtoV : ∀ q ∈ U, realEmbed q ∈ V := by
    intro q hq
    exact hball hq
  have henergy : ∀ x, AnalyticOnNhd ℝ (energy x) U := by
    intro x q hq
    exact analyticAt_re_comp_realEmbed (hbranchA x _ (hUtoV q hq))
  have hbranchReal : ∀ q ∈ U, ∀ x,
      branch x (realEmbed q) = ((energy x q : ℝ) : ℂ) := by
    intro q hq x
    have hroot : matrixCharpolyRelation
        ((hypercubeTwoLocalFinPolynomialMatrix n).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) (realEmbed q)),
          branch x (realEmbed q)) = 0 := by
      exact hbranchRoot x (realEmbed q) (hUtoV q hq)
    have him : (branch x (realEmbed q)).im = 0 := by
      apply matrixCharpolyRelation_im_eq_zero_of_isHermitian
        ((hypercubeTwoLocalFinPolynomialMatrix n).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) (realEmbed q)))
      · change ((hypercubeTwoLocalFinPolynomialMatrix n).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) fun t => (q t : ℂ))).IsHermitian
        exact isHermitian_twoLocalFinEval q
      · exact hroot
    apply Complex.ext
    · rfl
    · simpa using him
  have henergyInj : ∀ q ∈ U, Function.Injective fun x => energy x q := by
    intro q hq x y hxy
    apply hbranchInj (realEmbed q) (hUtoV q hq)
    change branch x (realEmbed q) = branch y (realEmbed q)
    rw [hbranchReal q hq x, hbranchReal q hq y]
    exact congrArg (· : ℝ → ℂ) hxy
  have hescape : ∀ c : (Fin n → Bool) → ℝ,
      (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
        ∃ q ∈ U, (∑ x, c x * energy x q) ≠ target := by
    intro c hc target
    let W : Set (ℝ × ℝ) :=
      {q | ∀ i : Fin n, twoLocalFinRealEdgeSlice p i q ∈ U}
    have hW : W ∈ nhds ((0, 0) : ℝ × ℝ) := by
      change ∀ᶠ q in nhds ((0, 0) : ℝ × ℝ),
        ∀ i : Fin n, twoLocalFinRealEdgeSlice p i q ∈ U
      rw [Filter.eventually_all]
      intro i
      have hzero : twoLocalFinRealEdgeSlice p i (0, 0) = p₀ := by
        simpa [p₀] using twoLocalFinRealEdgeSlice_zero p i
      apply (continuous_twoLocalFinRealEdgeSlice p i).continuousAt.preimage_mem_nhds
      exact Metric.isOpen_ball.mem_nhds (by simpa [U, hzero] using hepsilon)
    obtain ⟨i, q, hqW, _hqV, hne⟩ :=
      exists_embeddedTwoLocalBranchAction_ne_const
        M embed (fun _ => 0) (continuous_pi fun _ => continuous_apply _)
        (by
          intro p' i' q'
          rw [show (((0 : ℝ) : ℂ)) •
            (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = 0 by simp, sub_zero]
          exact map_eval_embed_twoLocalFin (twoLocalEdgeSlice p' i' q'))
        p V branch htr hinj hgappos hgapinj hVopen hz₀V hbranchA hbranch0
        hbranchRoot W hW c hc target
    let q' := twoLocalFinRealEdgeSlice p i q
    have hq'U : q' ∈ U := hqW i
    have hsliceeq : realEmbed q' = embed (twoLocalEdgeSlice p i q) := by
      simpa [q', embed] using realEmbed_twoLocalFinRealEdgeSlice p i q
    refine ⟨q', hq'U, ?_⟩
    intro heq
    apply hne
    rw [← hsliceeq]
    calc
      ∑ x, (c x : ℂ) * branch x (realEmbed q') =
          ∑ x, (c x : ℂ) * ((energy x q' : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [hbranchReal q' hq'U x]
      _ = (((∑ x, c x * energy x q') : ℝ) : ℂ) := by
            push_cast
            rfl
      _ = (target : ℂ) := congrArg (· : ℝ → ℂ) heq
  exact ⟨U, p₀, energy, Metric.isOpen_ball,
    (convex_ball p₀ epsilon).isPreconnected, Metric.mem_ball_self hepsilon,
    henergy, henergyInj, hescape⟩

/-- **Optimal continuous recurrence exponent for ordinary two-local
Hamiltonians.**  For every qubit number at least two, one real open chart
of the time-independent all-qubit two-local ensemble has `2^N - 2`
projective spectral frequencies, and the parameters which fail the
optimal continuous first-return lower exponent have Lebesgue measure
zero in that same chart.  Writing the qubit number as `n + 2` makes the
statement unconditional, with no size premise. -/
theorem exists_twoLocalFin_optimalContinuousReturn_ae (n : ℕ) :
    ∃ (U : Set (Fin (Fintype.card
        (HypercubeTwoLocalParameter (n + 2))) → ℝ))
      (p₀ : Fin (Fintype.card
        (HypercubeTwoLocalParameter (n + 2))) → ℝ)
      (energy : Fin ((2 ^ (n + 2) - 2) + 2) →
        (Fin (Fintype.card
          (HypercubeTwoLocalParameter (n + 2))) → ℝ) → ℝ),
      IsOpen U ∧ IsPreconnected U ∧ p₀ ∈ U ∧
      (∀ i, AnalyticOnNhd ℝ (energy i) U) ∧
      (∀ q ∈ U, Function.Injective fun i => energy i q) ∧
      volume {q ∈ U |
        ¬ KleinbockMargulis.HasOptimalContinuousReturnLower
          (fun j : Fin (2 ^ (n + 2) - 2) =>
            anchoredProjectiveRatio energy q j)} = 0 ∧
      volume {q ∈ U |
        ¬ HasOptimalPhysicalContinuousReturnLower energy q} = 0 := by
  classical
  let N := n + 2
  letI : Nonempty (HypercubeTwoLocalParameter N) :=
    ⟨HypercubeTwoLocalParameter.constant⟩
  letI : NeZero (Fintype.card (HypercubeTwoLocalParameter N)) :=
    ⟨Fintype.card_ne_zero⟩
  obtain ⟨U, p₀, rawEnergy, hUopen, hUconn, hp₀U, hrawA,
      hrawInj, hrawEscape⟩ :=
    exists_twoLocalFinRealAnalyticChart_affineEscape N
  have hcard : Fintype.card (Fin N → Bool) = 2 ^ N := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have htwo : 2 ≤ 2 ^ N := by
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by simp [N])
  have hadd : (2 ^ N - 2) + 2 = Fintype.card (Fin N → Bool) := by
    rw [hcard]
    exact Nat.sub_add_cancel htwo
  let e : Fin ((2 ^ N - 2) + 2) ≃ (Fin N → Bool) :=
    (finCongr hadd).trans (Fintype.equivFin (Fin N → Bool)).symm
  let energy : Fin ((2 ^ N - 2) + 2) →
      (Fin (Fintype.card (HypercubeTwoLocalParameter N)) → ℝ) → ℝ :=
    fun i q => rawEnergy (e i) q
  have henergyA : ∀ i, AnalyticOnNhd ℝ (energy i) U := by
    intro i
    exact hrawA (e i)
  have henergyInj : ∀ q ∈ U, Function.Injective fun i => energy i q := by
    intro q hq i j hij
    apply e.injective
    exact hrawInj q hq hij
  have hescape : ∀ c : Fin ((2 ^ N - 2) + 2) → ℝ,
      (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
        ∃ q ∈ U, (∑ i, c i * energy i q) ≠ target := by
    intro c hc target
    let c' : (Fin N → Bool) → ℝ := fun x => c (e.symm x)
    have hc' : ¬ ∀ x y, c' x = c' y := by
      intro hconstant
      apply hc
      intro i j
      simpa [c'] using hconstant (e i) (e j)
    obtain ⟨q, hqU, hqne⟩ := hrawEscape c' hc' target
    refine ⟨q, hqU, ?_⟩
    have hsum : (∑ x, c' x * rawEnergy x q) =
        ∑ i, c i * energy i q := by
      exact Fintype.sum_equiv e.symm _ _ (fun x => by simp [c', energy])
    rwa [← hsum]
  have hr : 0 < 2 ^ N - 2 := by
    have hfour : 4 ≤ 2 ^ N := by
      calc
        4 = 2 ^ (2 : ℕ) := by norm_num
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by simp [N])
    omega
  have hden : ∀ q ∈ U, energy 1 q - energy 0 q ≠ 0 := by
    intro q hq
    rw [sub_ne_zero]
    intro heq
    have hindex : (1 : Fin ((2 ^ N - 2) + 2)) = 0 :=
      henergyInj q hq heq
    exact Fin.zero_ne_one hindex.symm
  refine ⟨U, p₀, energy, hUopen, hUconn, hp₀U, henergyA,
    henergyInj, ?_, ?_⟩
  · simpa [N] using
      (volume_not_optimalReturn_anchoredProjectiveRatio_eq_zero_of_affineEscape
        hr hUopen hUconn energy henergyA p₀ hp₀U hden hescape)
  · simpa [N] using
      (volume_not_optimalPhysicalReturn_eq_zero_of_affineEscape
        hr hUopen hUconn energy henergyA p₀ hp₀U hden hescape)

end

end GaloisForLFunctions.HTGeometry
