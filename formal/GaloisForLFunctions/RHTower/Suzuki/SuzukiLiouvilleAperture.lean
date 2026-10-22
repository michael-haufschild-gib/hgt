import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureAlmostEvery
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Dense relative-Liouville apertures

The displacement group of a finite prime alphabet is dense in the line, so for every rate the
apertures approximated faster than that rate form a dense open set: removing the finitely many
short valuations leaves a dense set of centres, and each contributes an interval.  Baire's theorem
then produces a dense set of apertures approximated infinitely often at *every* rate — the
relative-Liouville apertures.  At such an aperture no exponentially tempered orbit weight can hold
the endpoint activations inside a positive Gamma strip.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

variable {P : Type*} [Fintype P]

/-- The apertures approximated at rate `f` by some valuation of length at least `n`. -/
def liouvilleStage (ℓ : (P → ℤ) → ℝ) (f : ℕ → ℝ) (n : ℕ) : Set ℝ :=
  ⋃ ν : P → ℤ, ⋃ _ : n ≤ orbitLength ν,
    {a : ℝ | 0 < |2 * a - ℓ ν| ∧ |2 * a - ℓ ν| < f (orbitLength ν)}

theorem isOpen_liouvilleStage (ℓ : (P → ℤ) → ℝ) (f : ℕ → ℝ) (n : ℕ) :
    IsOpen (liouvilleStage ℓ f n) := by
  refine isOpen_iUnion fun ν => isOpen_iUnion fun _ => ?_
  have hcont : Continuous fun a : ℝ => |2 * a - ℓ ν| := by fun_prop
  exact (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)

/-- Long valuations still have dense displacement, because only finitely many are short. -/
theorem dense_longDisplacements [DecidableEq P] {ℓ : (P → ℤ) → ℝ} (hdense : Dense (Set.range ℓ))
    (hinj : Function.Injective ℓ) (n : ℕ) :
    Dense {x : ℝ | ∃ ν : P → ℤ, n ≤ orbitLength ν ∧ ℓ ν = x} := by
  have hfin : {x : ℝ | ∃ ν : P → ℤ, orbitLength ν < n ∧ ℓ ν = x}.Finite := by
    have hsub : {x : ℝ | ∃ ν : P → ℤ, orbitLength ν < n ∧ ℓ ν = x}
        ⊆ ℓ '' (⋃ N ∈ Finset.range n, (orbitLevel P N : Set (P → ℤ))) := by
      rintro x ⟨ν, hν, rfl⟩
      refine ⟨ν, ?_, rfl⟩
      rw [mem_iUnion₂]
      exact ⟨orbitLength ν, Finset.mem_range.mpr hν, mem_orbitLevel rfl⟩
    refine Set.Finite.subset (Set.Finite.image ℓ ?_) hsub
    refine Set.Finite.biUnion (Finset.range n).finite_toSet fun N _ => ?_
    exact (orbitLevel P N).finite_toSet
  have hcompl : {x : ℝ | ∃ ν : P → ℤ, n ≤ orbitLength ν ∧ ℓ ν = x}
      = Set.range ℓ \ {x : ℝ | ∃ ν : P → ℤ, orbitLength ν < n ∧ ℓ ν = x} := by
    ext x
    constructor
    · rintro ⟨ν, hν, rfl⟩
      refine ⟨⟨ν, rfl⟩, ?_⟩
      rintro ⟨μ, hμ, hμx⟩
      have : μ = ν := hinj hμx
      rw [this] at hμ
      omega
    · rintro ⟨⟨ν, rfl⟩, hx⟩
      refine ⟨ν, ?_, rfl⟩
      by_contra hlt
      exact hx ⟨ν, by omega, rfl⟩
  rw [hcompl]
  exact hdense.sdiff_finite hfin

/-- **`(28)`, one stage: each approximation stage is dense.** -/
theorem dense_liouvilleStage [DecidableEq P] {ℓ : (P → ℤ) → ℝ} (hdense : Dense (Set.range ℓ))
    (hinj : Function.Injective ℓ) {f : ℕ → ℝ} (hf : ∀ n, 0 < f n) (n : ℕ) :
    Dense (liouvilleStage ℓ f n) := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hdenseLong := dense_longDisplacements hdense hinj n
  obtain ⟨y, hyball, hy⟩ := (Metric.dense_iff.mp hdenseLong) (2 * x₀) (ε) hε
  obtain ⟨ν, hνlen, rfl⟩ := hy
  set δ : ℝ := min (f (orbitLength ν)) ε with hδ
  have hδpos : 0 < δ := lt_min (hf _) hε
  refine ⟨ℓ ν / 2 + δ / 4, ?_, ?_⟩
  · apply hball
    rw [Metric.mem_ball]
    have hdist : dist (ℓ ν) (2 * x₀) < ε := hyball
    have hδε : δ ≤ ε := min_le_right _ _
    rw [Real.dist_eq, abs_lt] at hdist ⊢
    constructor <;> [linarith [hdist.1, hdist.2]; linarith [hdist.1, hdist.2]]
  · simp only [liouvilleStage, mem_iUnion]
    refine ⟨ν, hνlen, ?_, ?_⟩
    · have hval : 2 * (ℓ ν / 2 + δ / 4) - ℓ ν = δ / 2 := by ring
      rw [hval, abs_of_pos (by linarith)]
      linarith
    · have hval : 2 * (ℓ ν / 2 + δ / 4) - ℓ ν = δ / 2 := by ring
      rw [hval, abs_of_pos (by linarith)]
      have hfle : δ ≤ f (orbitLength ν) := min_le_left _ _
      linarith

/-- **`(28)`: relative-Liouville apertures are dense.** -/
theorem dense_liouvilleApertures [DecidableEq P] {ℓ : (P → ℤ) → ℝ} (hdense : Dense (Set.range ℓ))
    (hinj : Function.Injective ℓ) {f : ℕ → ℝ} (hf : ∀ n, 0 < f n) :
    Dense (⋂ n : ℕ, liouvilleStage ℓ f n) :=
  dense_iInter_of_isOpen (fun n => isOpen_liouvilleStage ℓ f n)
    (fun n => dense_liouvilleStage hdense hinj hf n)

/-- At a relative-Liouville aperture the approximations have unbounded length. -/
theorem exists_long_approximant {ℓ : (P → ℤ) → ℝ} {f : ℕ → ℝ} {a : ℝ}
    (ha : a ∈ ⋂ n : ℕ, liouvilleStage ℓ f n) (n : ℕ) :
    ∃ ν : P → ℤ, n ≤ orbitLength ν ∧ 0 < |2 * a - ℓ ν| ∧ |2 * a - ℓ ν| < f (orbitLength ν) := by
  have han := mem_iInter.mp ha n
  rw [liouvilleStage, mem_iUnion] at han
  obtain ⟨ν, hν⟩ := han
  rw [mem_iUnion] at hν
  obtain ⟨hlen, hlt⟩ := hν
  exact ⟨ν, hlen, hlt.1, hlt.2⟩

/-- The super-exponential rate of the Liouville stages. -/
def liouvilleRate (N : ℕ) : ℝ := Real.exp (-((N : ℝ) ^ (2 : ℕ)))

theorem liouvilleRate_pos (N : ℕ) : 0 < liouvilleRate N := Real.exp_pos _

/-- A super-exponentially close approximant is exponentially deep. -/
theorem sq_lt_apertureDepth {ℓ : (P → ℤ) → ℝ} {a : ℝ} {ν : P → ℤ}
    (hpos : 0 < |2 * a - ℓ ν|) (hlt : |2 * a - ℓ ν| < liouvilleRate (orbitLength ν)) :
    ((orbitLength ν : ℝ)) ^ (2 : ℕ) < apertureDepth a ℓ ν := by
  have hlog : Real.log (apertureDefect a ℓ ν) < -((orbitLength ν : ℝ) ^ (2 : ℕ)) := by
    have hdef : apertureDefect a ℓ ν = |2 * a - ℓ ν| := rfl
    rw [hdef]
    have := Real.log_lt_log hpos hlt
    rwa [liouvilleRate, Real.log_exp] at this
  rw [apertureDepth]
  linarith

/-- The exponential barrier grows without bound along the lattice. -/
theorem tendsto_liouvilleBarrier {σ C w₀ : ℝ} (hσ : 0 < σ) (hC : 0 < C) (hw₀ : 0 < w₀) :
    Filter.Tendsto (fun N : ℕ => w₀ * (Real.exp (σ * (N : ℝ) ^ (2 : ℕ)) * C ^ N)) Filter.atTop
      Filter.atTop := by
  have hcast : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlin : Filter.Tendsto (fun N : ℕ => σ * (N : ℝ) + Real.log C) Filter.atTop
      Filter.atTop := by
    exact Filter.tendsto_atTop_add_const_right _ (Real.log C) (hcast.const_mul_atTop hσ)
  have hprod : Filter.Tendsto (fun N : ℕ => (N : ℝ) * (σ * (N : ℝ) + Real.log C))
      Filter.atTop Filter.atTop := hcast.atTop_mul_atTop₀ hlin
  have hexp : Filter.Tendsto
      (fun N : ℕ => Real.exp ((N : ℝ) * (σ * (N : ℝ) + Real.log C))) Filter.atTop
      Filter.atTop := Real.tendsto_exp_atTop.comp hprod
  have hscaled := hexp.const_mul_atTop hw₀
  refine hscaled.congr fun N => ?_
  have hpow : C ^ N = Real.exp ((N : ℝ) * Real.log C) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [hpow, ← Real.exp_add]
  congr 2
  ring

/-! ## `(29)` implies `(30)`: bounded edge ratios force an exponential lower bound -/

/-- Removing one unit from a nonzero coordinate shortens the `ℓ¹` length by one. -/
theorem orbitLength_sub_unit [DecidableEq P] {ν : P → ℤ} {p : P} {ε : ℤ} (hp : ν p ≠ 0)
    (hε : ε = if 0 < ν p then 1 else -1) :
    orbitLength (ν + (Pi.single p (-ε) : P → ℤ)) + 1 = orbitLength ν := by
  classical
  have happ : ∀ q : P, (ν + (Pi.single p (-ε) : P → ℤ)) q
      = ν q + (Pi.single p (-ε) : P → ℤ) q := fun q => Pi.add_apply _ _ q
  have hpval : (ν + (Pi.single p (-ε) : P → ℤ)) p = ν p - ε := by
    rw [happ p, Pi.single_eq_same]
    ring
  have hqval : ∀ q, q ≠ p → (ν + (Pi.single p (-ε) : P → ℤ)) q = ν q := by
    intro q hq
    rw [happ q, Pi.single_eq_of_ne hq]
    ring
  rw [orbitLength, orbitLength,
    ← Finset.sum_erase_add _ (fun q => ((ν + (Pi.single p (-ε) : P → ℤ)) q).natAbs)
      (Finset.mem_univ p),
    ← Finset.sum_erase_add _ (fun q => (ν q).natAbs) (Finset.mem_univ p)]
  have heq : (∑ q ∈ Finset.univ.erase p, ((ν + (Pi.single p (-ε) : P → ℤ)) q).natAbs)
      = ∑ q ∈ Finset.univ.erase p, (ν q).natAbs :=
    Finset.sum_congr rfl fun q hq => by rw [hqval q (Finset.ne_of_mem_erase hq)]
  rw [heq, hpval]
  have hmain : (ν p - ε).natAbs + 1 = (ν p).natAbs := by
    subst hε
    by_cases hpos : 0 < ν p
    · rw [if_pos hpos]
      omega
    · rw [if_neg hpos]
      omega
  omega

/-- **`(30)`: a weight with bounded inverse edge ratios decays at most exponentially.** -/
theorem weight_ge_of_edge_bound [DecidableEq P] {w : (P → ℤ) → ℝ} {C : ℝ} (hC : 0 < C)
    (hstep : ∀ (μ : P → ℤ) (p : P) (ε : ℤ), ε = 1 ∨ ε = -1 → w μ ≤ C * w (μ + Pi.single p ε))
    (ν : P → ℤ) : w 0 ≤ C ^ orbitLength ν * w ν := by
  classical
  generalize hn : orbitLength ν = n
  induction n generalizing ν with
  | zero =>
      have hzero : ν = 0 := by
        funext p
        have hsum : ∑ q, (ν q).natAbs = 0 := hn
        have hq : (ν p).natAbs = 0 := Finset.sum_eq_zero_iff.mp hsum p (Finset.mem_univ p)
        show ν p = (0 : P → ℤ) p
        rw [Pi.zero_apply]
        omega
      rw [hzero, pow_zero, one_mul]
  | succ k ih =>
      have hne : ν ≠ 0 := by
        intro h
        rw [h] at hn
        simp [orbitLength] at hn
      obtain ⟨p, hp⟩ : ∃ p : P, ν p ≠ 0 := by
        by_contra hall
        apply hne
        funext q
        show ν q = (0 : P → ℤ) q
        rw [Pi.zero_apply]
        by_contra hq
        exact hall ⟨q, hq⟩
      set ε : ℤ := if 0 < ν p then 1 else -1 with hε
      have hεunit : ε = 1 ∨ ε = -1 := by
        by_cases hpos : 0 < ν p
        · left
          rw [hε, if_pos hpos]
        · right
          rw [hε, if_neg hpos]
      set μ : P → ℤ := ν + (Pi.single p (-ε) : P → ℤ) with hμ
      have hlen : orbitLength μ = k := by
        have hsub := orbitLength_sub_unit (ν := ν) (p := p) (ε := ε) hp hε
        rw [hμ]
        omega
      have hstep' : w μ ≤ C * w (μ + Pi.single p ε) := hstep μ p ε hεunit
      have hback : μ + (Pi.single p ε : P → ℤ) = ν := by
        rw [hμ]
        funext q
        rw [Pi.add_apply, Pi.add_apply]
        by_cases hq : q = p
        · subst hq
          rw [Pi.single_eq_same, Pi.single_eq_same]
          ring
        · rw [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne hq]
          ring
      rw [hback] at hstep'
      have hih := ih μ hlen
      calc w 0 ≤ C ^ k * w μ := hih
        _ ≤ C ^ k * (C * w ν) := by
            apply mul_le_mul_of_nonneg_left hstep'
            positivity
        _ = C ^ (k + 1) * w ν := by
            rw [pow_succ]
            ring

/-- **`(31)`: at a relative-Liouville aperture no tempered weight survives the Gamma strip.**
The activation of an approximant of length `N` is at least `w₀ exp(σN²) C^N`, which is unbounded,
so no positive Gamma weight can hold all endpoint activations. -/
theorem liouville_activation_unbounded {ℓ : (P → ℤ) → ℝ} {a σ C w₀ : ℝ}
    (hσ : 0 < σ) (hC : 0 < C) (hw₀ : 0 < w₀)
    (ha : a ∈ ⋂ n : ℕ, liouvilleStage ℓ liouvilleRate n)
    (w : (P → ℤ) → ℝ) (hw : ∀ ν, w₀ * C ^ orbitLength ν ≤ w ν) (M : ℝ) :
    ∃ ν : P → ℤ, M ≤ Real.exp (σ * apertureDepth a ℓ ν) * w ν := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    ((tendsto_liouvilleBarrier hσ hC hw₀).eventually_ge_atTop M)
  obtain ⟨ν, hlen, hpos, hlt⟩ := exists_long_approximant ha n
  refine ⟨ν, ?_⟩
  have hbar := hn (orbitLength ν) hlen
  have hdepth := sq_lt_apertureDepth hpos hlt
  have hexp : Real.exp (σ * (orbitLength ν : ℝ) ^ (2 : ℕ))
      ≤ Real.exp (σ * apertureDepth a ℓ ν) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hdepth.le hσ.le
  have hwν : w₀ * C ^ orbitLength ν ≤ w ν := hw ν
  have hposC : (0:ℝ) < C ^ orbitLength ν := pow_pos hC _
  calc M ≤ w₀ * (Real.exp (σ * (orbitLength ν : ℝ) ^ (2 : ℕ)) * C ^ orbitLength ν) := hbar
    _ = Real.exp (σ * (orbitLength ν : ℝ) ^ (2 : ℕ)) * (w₀ * C ^ orbitLength ν) := by ring
    _ ≤ Real.exp (σ * apertureDepth a ℓ ν) * (w₀ * C ^ orbitLength ν) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ Real.exp (σ * apertureDepth a ℓ ν) * w ν :=
        mul_le_mul_of_nonneg_left hwν (Real.exp_pos _).le

end

end RHTower
