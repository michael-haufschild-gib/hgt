import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Deterministic localization-to-spectral-tail transfer

This file isolates the exact deterministic input needed to turn exponential
eigenfunction localization into a bound on the spectral weight invisible
outside a chosen localization radius.

It does **not** prove localization for an Anderson Hamiltonian.  A concrete
random or deterministic operator must separately supply:

* a site-labelled eigenbasis;
* the pointwise weight estimate
  `p k ≤ C * exp (-2 * μ * radius k)`; and
* a shell-cardinality estimate.

The capstone then shows that the omitted normalized spectral mass is bounded
by a geometric tail.  This is the honest interface by which a model-specific
Anderson localization theorem can feed an observer-recurrence theorem.
-/

open Finset

namespace RHTower

noncomputable section

variable {κ : Type*} [Fintype κ]

/-- Spectral weight carried by modes whose localization centres lie strictly
outside radius `R`.  The function `radius` is deliberately abstract: in a
model-specific application it is the lattice distance from a fixed observer
site to the localization centre labelling the eigenmode. -/
def finiteLocalizedSpectralTail
    (p : κ → ℝ) (radius : κ → ℕ) (R : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => R < radius k), p k

/-- Modes whose localization centres lie on the exact shell `m`. -/
def finiteLocalizationShell
    (radius : κ → ℕ) (m : ℕ) : Finset κ :=
  Finset.univ.filter (fun k => radius k = m)

/-- The exact pointwise exponential envelope summed over modes outside `R`. -/
def finiteLocalizationExponentialEnvelope
    (C μ : ℝ) (radius : κ → ℕ) (R : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => R < radius k),
    C * Real.exp (-2 * μ * (radius k : ℝ))

/-- Any pointwise localization estimate transfers directly to the omitted
spectral mass.  No normalization or positivity of `p` is required for this
upper bound. -/
theorem finiteLocalizedSpectralTail_le_exponentialEnvelope
    (p : κ → ℝ) (radius : κ → ℕ) (R : ℕ) (C μ : ℝ)
    (hdecay :
      ∀ k, p k ≤ C * Real.exp (-2 * μ * (radius k : ℝ))) :
    finiteLocalizedSpectralTail p radius R ≤
      finiteLocalizationExponentialEnvelope C μ radius R := by
  unfold finiteLocalizedSpectralTail finiteLocalizationExponentialEnvelope
  exact Finset.sum_le_sum fun k _hk => hdecay k

/-- A finite sum of powers whose exponents all start at `N` is bounded by the
full geometric tail beginning at `N`. -/
theorem finite_sum_pow_le_geometric_tail
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (N : ℕ) (M : Finset ℕ) (hM : ∀ m ∈ M, N ≤ m) :
    ∑ m ∈ M, s ^ m ≤ s ^ N * (1 - s)⁻¹ := by
  let T : Finset ℕ := M.image (fun m => m - N)
  have hsum :
      (∑ m ∈ M, s ^ m) = ∑ n ∈ T, s ^ (n + N) := by
    apply Finset.sum_bij (fun m _hm => m - N)
    · intro m hm
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
    · intro a ha b hb hab
      have haN := hM a ha
      have hbN := hM b hb
      omega
    · intro n hn
      obtain ⟨m, hm, hmn⟩ := Finset.mem_image.mp hn
      exact ⟨m, hm, hmn⟩
    · intro m hm
      rw [Nat.sub_add_cancel (hM m hm)]
  rw [hsum]
  have hsumGeo : Summable (fun n : ℕ => s ^ (n + N)) := by
    have hgeo := summable_geometric_of_lt_one hs0 hs1
    simpa [pow_add, mul_comm] using hgeo.mul_left (s ^ N)
  calc
    ∑ n ∈ T, s ^ (n + N) ≤ ∑' n : ℕ, s ^ (n + N) := by
      exact hsumGeo.sum_le_tsum T
        (fun n _hn => pow_nonneg hs0 (n + N))
    _ = s ^ N * ∑' n : ℕ, s ^ n := by
      have hfun :
          (fun n : ℕ => s ^ (n + N)) =
            fun n : ℕ => s ^ N * s ^ n := by
        funext n
        rw [pow_add, mul_comm]
      rw [hfun, tsum_mul_left]
    _ = s ^ N * (1 - s)⁻¹ := by
      rw [tsum_geometric_of_lt_one hs0 hs1]

/-- **Shell-geometric localization transfer.**  Suppose mode weights obey
`p k ≤ C q^(radius k)`, while the number of localization centres on shell
`m` is at most `A B^m`.  If spatial shell growth loses to localization decay,
`B q < 1`, then the omitted weight outside `R` is bounded by the full
geometric tail beginning at `R + 1`.

This theorem is deterministic and finite-volume.  Its bound is independent of
the ambient number of modes once `A`, `B`, `C`, and `q` are uniform. -/
theorem finiteLocalizedSpectralTail_le_shellGeometric
    (p : κ → ℝ) (radius : κ → ℕ) (R : ℕ)
    (C q A B : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * q < 1)
    (hdecay : ∀ k, p k ≤ C * q ^ radius k)
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤ A * B ^ m) :
    finiteLocalizedSpectralTail p radius R ≤
      A * C * (B * q) ^ (R + 1) * (1 - B * q)⁻¹ := by
  let O : Finset κ :=
    Finset.univ.filter (fun k => R < radius k)
  let M : Finset ℕ := O.image radius
  have hgroup :
      finiteLocalizedSpectralTail p radius R =
        ∑ m ∈ M, ∑ k ∈ O with radius k = m, p k := by
    unfold finiteLocalizedSpectralTail
    change (∑ k ∈ O, p k) = _
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun k hk => Finset.mem_image.mpr ⟨k, hk, rfl⟩) p
  have hM : ∀ m ∈ M, R + 1 ≤ m := by
    intro m hm
    obtain ⟨k, hkO, hkm⟩ := Finset.mem_image.mp hm
    have hkR : R < radius k := (Finset.mem_filter.mp hkO).2
    omega
  have hs : 0 ≤ B * q := mul_nonneg hB hq
  have hpow := finite_sum_pow_le_geometric_tail
    (B * q) hs hcontract (R + 1) M hM
  rw [hgroup]
  calc
    ∑ m ∈ M, ∑ k ∈ O with radius k = m, p k ≤
        ∑ m ∈ M, A * C * (B * q) ^ m := by
      apply Finset.sum_le_sum
      intro m _hm
      let F : Finset κ := O.filter (fun k => radius k = m)
      have hFsubset : F ⊆ finiteLocalizationShell radius m := by
        intro k hk
        have hkr : radius k = m := (Finset.mem_filter.mp hk).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hkr⟩
      have hcard :
          (F.card : ℝ) ≤ (finiteLocalizationShell radius m).card := by
        exact_mod_cast Finset.card_le_card hFsubset
      calc
        ∑ k ∈ O with radius k = m, p k ≤
            ∑ _k ∈ O with radius _k = m, C * q ^ m := by
          apply Finset.sum_le_sum
          intro k hk
          have hkr : radius k = m := (Finset.mem_filter.mp hk).2
          simpa [hkr] using hdecay k
        _ = (F.card : ℝ) * (C * q ^ m) := by
          simp [F]
        _ ≤ ((finiteLocalizationShell radius m).card : ℝ) *
              (C * q ^ m) := by
          exact mul_le_mul_of_nonneg_right hcard
            (mul_nonneg hC (pow_nonneg hq m))
        _ ≤ (A * B ^ m) * (C * q ^ m) := by
          exact mul_le_mul_of_nonneg_right (hshell m)
            (mul_nonneg hC (pow_nonneg hq m))
        _ = A * C * (B * q) ^ m := by
          rw [mul_pow]
          ring
    _ = A * C * ∑ m ∈ M, (B * q) ^ m := by
      rw [Finset.mul_sum]
    _ ≤ A * C *
          ((B * q) ^ (R + 1) * (1 - B * q)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hA hC)
    _ = A * C * (B * q) ^ (R + 1) *
          (1 - B * q)⁻¹ := by
      ring

/-- Exponential-eigenfunction form of the shell-geometric transfer.  The
site weight estimate is the square-amplitude estimate
`p k ≤ C exp(-2 μ radius(k))`. -/
theorem finiteLocalizedSpectralTail_le_shellExponential
    (p : κ → ℝ) (radius : κ → ℕ) (R : ℕ)
    (C μ A B : ℝ)
    (hC : 0 ≤ C) (hμ : 0 < μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ k, p k ≤ C * Real.exp (-2 * μ * (radius k : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤ A * B ^ m) :
    finiteLocalizedSpectralTail p radius R ≤
      A * C * (B * Real.exp (-2 * μ)) ^ (R + 1) *
        (1 - B * Real.exp (-2 * μ))⁻¹ := by
  have _hq_lt_one : Real.exp (-2 * μ) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  apply finiteLocalizedSpectralTail_le_shellGeometric
    p radius R C (Real.exp (-2 * μ)) A B
    hC (Real.exp_nonneg _) hA hB hcontract
  · intro k
    have hexp :
        Real.exp (-2 * μ * (radius k : ℝ)) =
          Real.exp (-2 * μ) ^ radius k := by
      rw [show -2 * μ * (radius k : ℝ) =
          (radius k : ℝ) * (-2 * μ) by ring]
      exact Real.exp_nat_mul (-2 * μ) (radius k)
    rw [← hexp]
    simpa only [neg_mul] using hdecay k
  · exact hshell

/-- A normalized nonnegative spectral packet has tail mass between zero and
one, independently of localization. -/
theorem finiteLocalizedSpectralTail_mem_unitInterval
    (p : κ → ℝ) (radius : κ → ℕ) (R : ℕ)
    (hp : ∀ k, 0 ≤ p k)
    (hnorm : ∑ k, p k = 1) :
    0 ≤ finiteLocalizedSpectralTail p radius R ∧
      finiteLocalizedSpectralTail p radius R ≤ 1 := by
  constructor
  · unfold finiteLocalizedSpectralTail
    exact Finset.sum_nonneg fun k _hk => hp k
  · unfold finiteLocalizedSpectralTail
    calc
      ∑ k ∈ Finset.univ.filter (fun k => R < radius k), p k ≤
          ∑ k ∈ Finset.univ, p k := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun k _hk _hnot => hp k)
      _ = 1 := hnorm

/-- **Deterministic Anderson-locality tail law.**  For normalized site
weights with an exponentially localized site-labelled eigenbasis and a
uniform shell-growth bound, observer-invisible spectral mass outside radius
`R` is at most the smaller of total mass one and an explicit geometric tail.

This is a transfer theorem, not a proof that any Anderson ensemble satisfies
its localization and shell hypotheses. -/
theorem finiteAndersonLocalizationTailLaw
    (p : κ → ℝ) (radius : κ → ℕ) (R : ℕ)
    (C μ A B : ℝ)
    (hp : ∀ k, 0 ≤ p k)
    (hnorm : ∑ k, p k = 1)
    (hC : 0 ≤ C) (hμ : 0 < μ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcontract : B * Real.exp (-2 * μ) < 1)
    (hdecay :
      ∀ k, p k ≤ C * Real.exp (-2 * μ * (radius k : ℝ)))
    (hshell :
      ∀ m,
        ((finiteLocalizationShell radius m).card : ℝ) ≤ A * B ^ m) :
    0 ≤ finiteLocalizedSpectralTail p radius R ∧
      finiteLocalizedSpectralTail p radius R ≤
        min 1
          (A * C * (B * Real.exp (-2 * μ)) ^ (R + 1) *
            (1 - B * Real.exp (-2 * μ))⁻¹) := by
  have hunit :=
    finiteLocalizedSpectralTail_mem_unitInterval
      p radius R hp hnorm
  refine ⟨hunit.1, le_min hunit.2 ?_⟩
  exact finiteLocalizedSpectralTail_le_shellExponential
    p radius R C μ A B hC hμ hA hB hcontract hdecay hshell

end

end RHTower
