import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Residues over a divergent reference weight, and the profiles that read them

Fix a reference weight `h` on an index type.  A field `a` has *residue* `c`
over `h` when `a - c h` is summable.  When `h` is not summable the residue is
unique, so the fields possessing a residue form the direct sum of the summable
fields and the line spanned by `h`, and the residue is the coordinate on that
line.  Uniqueness needs nothing but divergence of `h`.

A *cofinal unit profile* for `h` is a family of weights with values in `[0,1]`,
unit `h`-mass, and supports eventually avoiding every finite set.  Averaging a
field against such a family recovers its residue: the reference part
contributes its coefficient exactly at every stage, while a summable part is
squeezed into a vanishing tail by the escaping supports.  Only boundedness,
normalization and escape are used, so any construction with those three
properties reads the same coordinate.

Every strictly positive divergent weight on the natural numbers admits such a
family: fill a window of consecutive indices until the accumulated mass reaches
one and give the last index the fractional weight that makes the mass exactly
one.  Hence the residue is always a limit of bounded cofinal averages.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

/-! ## The residue over a reference weight -/

/-- `a` has residue `c` over the reference weight `h` when `a` differs from the
`c`-multiple of `h` by a summable field. -/
def HasReferenceResidue (h : ι → ℝ) (a : ι → ℂ) (c : ℂ) : Prop :=
  Summable fun i => a i - c * (h i : ℂ)

theorem hasReferenceResidue_zero_iff (h : ι → ℝ) (a : ι → ℂ) :
    HasReferenceResidue h a 0 ↔ Summable a := by
  simp [HasReferenceResidue]

theorem hasReferenceResidue_self (h : ι → ℝ) :
    HasReferenceResidue h (fun i => (h i : ℂ)) 1 := by
  simp [HasReferenceResidue]

theorem HasReferenceResidue.add {h : ι → ℝ} {a b : ι → ℂ} {c d : ℂ}
    (ha : HasReferenceResidue h a c) (hb : HasReferenceResidue h b d) :
    HasReferenceResidue h (fun i => a i + b i) (c + d) := by
  refine (Summable.add ha hb).congr fun i => ?_
  ring

theorem HasReferenceResidue.const_mul {h : ι → ℝ} {a : ι → ℂ} {c : ℂ} (k : ℂ)
    (ha : HasReferenceResidue h a c) :
    HasReferenceResidue h (fun i => k * a i) (k * c) := by
  refine (Summable.mul_left k ha).congr fun i => ?_
  ring

/-- Residues do not see summable perturbations of the field. -/
theorem HasReferenceResidue.of_summable_sub {h : ι → ℝ} {a b : ι → ℂ} {c : ℂ}
    (hb : HasReferenceResidue h b c) (hab : Summable fun i => a i - b i) :
    HasReferenceResidue h a c := by
  refine (Summable.add hab hb).congr fun i => ?_
  ring

/-- **Divergence forces a unique residue.**  A field cannot represent two
different multiples of a non-summable reference weight. -/
theorem HasReferenceResidue.unique {h : ι → ℝ} {a : ι → ℂ} {c d : ℂ}
    (hns : ¬ Summable h) (hc : HasReferenceResidue h a c)
    (hd : HasReferenceResidue h a d) : c = d := by
  by_contra hne
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hsub : Summable fun i => (d - c) * (h i : ℂ) := by
    refine (Summable.sub hc hd).congr fun i => ?_
    ring
  have hcx : Summable fun i => ((h i : ℝ) : ℂ) := by
    refine (hsub.mul_left (d - c)⁻¹).congr fun i => ?_
    exact inv_mul_cancel_left₀ hdc _
  exact hns (Complex.summable_ofReal.mp hcx)

/-! ## Cofinal unit profiles -/

/-- A cofinal unit profile for the reference weight `h`: every stage takes
values in `[0,1]`, has unit `h`-mass, and the stages eventually vanish on every
finite set. -/
structure IsCofinalUnitProfile (h : ι → ℝ) (mu : ℕ → ι → ℝ) : Prop where
  nonneg : ∀ N i, 0 ≤ mu N i
  le_one : ∀ N i, mu N i ≤ 1
  hasSum_mass : ∀ N, HasSum (fun i => mu N i * h i) 1
  escapes : ∀ s : Finset ι, ∀ᶠ N in atTop, ∀ i ∈ s, mu N i = 0

/-- Average of a field against one stage of a profile. -/
noncomputable def profileAverage (mu : ℕ → ι → ℝ) (N : ℕ) (a : ι → ℂ) : ℂ :=
  ∑' i, (mu N i : ℂ) * a i

section Profile

variable {h : ι → ℝ} {mu : ℕ → ι → ℝ}

theorem norm_profileTerm_le (hmu : IsCofinalUnitProfile h mu) (N : ℕ)
    (a : ι → ℂ) (i : ι) : ‖(mu N i : ℂ) * a i‖ ≤ ‖a i‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hmu.nonneg N i)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hmu.le_one N i)

theorem summable_profileTerm (hmu : IsCofinalUnitProfile h mu) {a : ι → ℂ}
    (ha : Summable a) (N : ℕ) : Summable fun i => (mu N i : ℂ) * a i :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => norm_profileTerm_le hmu N a i) ha.norm)

/-- Every stage of a unit profile evaluates the reference weight to one. -/
theorem hasSum_profileReference (hmu : IsCofinalUnitProfile h mu) (N : ℕ) :
    HasSum (fun i => (mu N i : ℂ) * (h i : ℂ)) 1 := by
  have h1 := Complex.hasSum_ofReal.mpr (hmu.hasSum_mass N)
  simpa [Complex.ofReal_mul] using h1

theorem profileAverage_reference (hmu : IsCofinalUnitProfile h mu) (N : ℕ) :
    profileAverage mu N (fun i => (h i : ℂ)) = 1 :=
  (hasSum_profileReference hmu N).tsum_eq

/-- Splitting a field into its reference part and its summable remainder splits
the average into the coefficient and the average of the remainder. -/
theorem profileAverage_eq_add_remainder (hmu : IsCofinalUnitProfile h mu)
    {a : ι → ℂ} {c : ℂ} (hres : HasReferenceResidue h a c) (N : ℕ) :
    profileAverage mu N a =
      c + profileAverage mu N (fun i => a i - c * (h i : ℂ)) := by
  have hb : Summable fun i => a i - c * (h i : ℂ) := hres
  have href : HasSum (fun i => c * ((mu N i : ℂ) * (h i : ℂ))) c := by
    simpa using (hasSum_profileReference hmu N).mul_left c
  have hrem := (summable_profileTerm hmu hb N).hasSum
  have hadd := href.add hrem
  refine (hadd.congr_fun fun i => ?_).tsum_eq
  ring

/-- The average of a summable field over a finite-set-avoiding stage is bounded
by the mass of that field outside the avoided set. -/
theorem norm_profileAverage_le_tsum_compl (hmu : IsCofinalUnitProfile h mu)
    {b : ι → ℂ} (hb : Summable b) (N : ℕ) (s : Finset ι)
    (hs : ∀ i ∈ s, mu N i = 0) :
    ‖profileAverage mu N b‖ ≤ ∑' i : { x // x ∉ (s : Set ι) }, ‖b i‖ := by
  have hterm := summable_profileTerm hmu hb N
  have hnorm : Summable fun i => ‖(mu N i : ℂ) * b i‖ := hterm.norm
  have hzero : ∑ i ∈ s, ‖(mu N i : ℂ) * b i‖ = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [hs i hi]
  have hsplit := hnorm.sum_add_tsum_subtype_compl s
  rw [hzero, zero_add] at hsplit
  calc
    ‖profileAverage mu N b‖ ≤ ∑' i, ‖(mu N i : ℂ) * b i‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ∑' i : { x // x ∉ (s : Set ι) }, ‖(mu N i : ℂ) * b i‖ := hsplit.symm
    _ ≤ ∑' i : { x // x ∉ (s : Set ι) }, ‖b i‖ :=
      (hnorm.subtype _).tsum_le_tsum
        (fun i => norm_profileTerm_le hmu N b i) (hb.norm.subtype _)

/-- Summable fields are invisible to cofinal averaging. -/
theorem tendsto_profileAverage_zero_of_summable
    (hmu : IsCofinalUnitProfile h mu) {b : ι → ℂ} (hb : Summable b) :
    Tendsto (fun N => profileAverage mu N b) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨s, hs⟩ :=
    ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero fun i => ‖b i‖)).2 ε hε).exists
  filter_upwards [hmu.escapes s] with N hN
  exact lt_of_le_of_lt
    (norm_profileAverage_le_tsum_compl hmu hb N s hN) hs

/-- **Cofinal unit profiles read the residue.**  Bounded, unit-mass, escaping
averages converge to the coefficient of the reference weight, for every field
that has one. -/
theorem tendsto_profileAverage (hmu : IsCofinalUnitProfile h mu)
    {a : ι → ℂ} {c : ℂ} (hres : HasReferenceResidue h a c) :
    Tendsto (fun N => profileAverage mu N a) atTop (𝓝 c) := by
  have hb : Summable fun i => a i - c * (h i : ℂ) := hres
  have hzero := tendsto_profileAverage_zero_of_summable hmu hb
  have hshift : Tendsto
      (fun N => c + profileAverage mu N fun i => a i - c * (h i : ℂ))
      atTop (𝓝 c) := by simpa using hzero.const_add c
  exact hshift.congr fun N =>
    (profileAverage_eq_add_remainder hmu hres N).symm

/-- Two profiles for the same reference weight read the same coordinate. -/
theorem tendsto_profileAverage_congr {nu : ℕ → ι → ℝ}
    (hmu : IsCofinalUnitProfile h mu) (hnu : IsCofinalUnitProfile h nu)
    {a : ι → ℂ} {c d : ℂ}
    (hc : Tendsto (fun N => profileAverage mu N a) atTop (𝓝 c))
    (hd : Tendsto (fun N => profileAverage nu N a) atTop (𝓝 d))
    (hres : ∃ e, HasReferenceResidue h a e) : c = d := by
  obtain ⟨e, he⟩ := hres
  have h1 : c = e := tendsto_nhds_unique hc (tendsto_profileAverage hmu he)
  have h2 : d = e := tendsto_nhds_unique hd (tendsto_profileAverage hnu he)
  rw [h1, h2]

end Profile

/-! ## The window profile of a divergent positive weight -/

/-- Fill the consecutive indices from `N` up to `m N`, then give `m N` the
fractional weight that makes the total `h`-mass exactly one. -/
noncomputable def unitWindowProfile (h : ℕ → ℝ) (m : ℕ → ℕ) (N n : ℕ) : ℝ :=
  if n ∈ Finset.Ico N (m N) then 1
  else if n = m N then (1 - ∑ i ∈ Finset.Ico N (m N), h i) / h (m N)
  else 0

section Window

variable {h : ℕ → ℝ} {m : ℕ → ℕ}

theorem unitWindowProfile_nonneg (hpos : ∀ n, 0 < h n)
    (hmlt : ∀ N, (∑ i ∈ Finset.Ico N (m N), h i) < 1) (N n : ℕ) :
    0 ≤ unitWindowProfile h m N n := by
  have hw : 0 ≤ (1 - ∑ i ∈ Finset.Ico N (m N), h i) / h (m N) :=
    div_nonneg (by linarith [hmlt N]) (hpos (m N)).le
  rw [unitWindowProfile]
  split_ifs
  · exact zero_le_one
  · exact hw
  · exact le_rfl

theorem unitWindowProfile_le_one (hpos : ∀ n, 0 < h n)
    (hmge : ∀ N, 1 ≤ (∑ i ∈ Finset.Ico N (m N), h i) + h (m N)) (N n : ℕ) :
    unitWindowProfile h m N n ≤ 1 := by
  have hw : (1 - ∑ i ∈ Finset.Ico N (m N), h i) / h (m N) ≤ 1 := by
    rw [div_le_one (hpos (m N))]
    linarith [hmge N]
  rw [unitWindowProfile]
  split_ifs
  · exact le_rfl
  · exact hw
  · exact zero_le_one

theorem unitWindowProfile_eq_zero_of_lt (hmN : ∀ N, N ≤ m N) {N n : ℕ}
    (hn : n < N) : unitWindowProfile h m N n = 0 := by
  have hA : n ∉ Finset.Ico N (m N) := by
    simp only [Finset.mem_Ico]
    omega
  have hB : n ≠ m N := by
    have := hmN N
    omega
  rw [unitWindowProfile, if_neg hA, if_neg hB]

theorem hasSum_unitWindowProfile_mass (hpos : ∀ n, 0 < h n)
    (hmN : ∀ N, N ≤ m N) (N : ℕ) :
    HasSum (fun n => unitWindowProfile h m N n * h n) 1 := by
  have hmNe : h (m N) ≠ 0 := (hpos (m N)).ne'
  have hzero : ∀ n, n ∉ Finset.Ico N (m N + 1) →
      unitWindowProfile h m N n * h n = 0 := by
    intro n hn
    have hA : n ∉ Finset.Ico N (m N) := by
      intro hmem
      obtain ⟨hlow, hhigh⟩ := Finset.mem_Ico.mp hmem
      exact hn (Finset.mem_Ico.mpr ⟨hlow, by omega⟩)
    have hB : n ≠ m N := by
      intro hEq
      subst hEq
      exact hn (Finset.mem_Ico.mpr ⟨hmN N, by omega⟩)
    rw [unitWindowProfile, if_neg hA, if_neg hB, zero_mul]
  have hsum : HasSum (fun n => unitWindowProfile h m N n * h n)
      (∑ n ∈ Finset.Ico N (m N + 1), unitWindowProfile h m N n * h n) :=
    hasSum_sum_of_ne_finset_zero hzero
  have hval : ∑ n ∈ Finset.Ico N (m N + 1),
      unitWindowProfile h m N n * h n = 1 := by
    rw [Finset.sum_Ico_succ_top (hmN N)]
    have h1 : ∑ n ∈ Finset.Ico N (m N), unitWindowProfile h m N n * h n =
        ∑ n ∈ Finset.Ico N (m N), h n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [unitWindowProfile, if_pos hn, one_mul]
    have h2 : unitWindowProfile h m N (m N) * h (m N) =
        1 - ∑ n ∈ Finset.Ico N (m N), h n := by
      rw [unitWindowProfile, if_neg (by simp), if_pos rfl,
        div_mul_cancel₀ _ hmNe]
    rw [h1, h2]
    ring
  rwa [hval] at hsum

end Window

/-- **Every divergent positive weight is read by a bounded cofinal profile.**
The window construction supplies one, so the residue over such a weight is
always a limit of bounded cofinal averages. -/
theorem exists_isCofinalUnitProfile {h : ℕ → ℝ} (hpos : ∀ n, 0 < h n)
    (hns : ¬ Summable h) : ∃ mu : ℕ → ℕ → ℝ, IsCofinalUnitProfile h mu := by
  classical
  have hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, h i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => (hpos n).le).mp hns
  have hreach : ∀ N : ℕ, ∃ M, 1 ≤ ∑ i ∈ Finset.Ico N M, h i := by
    intro N
    obtain ⟨n, hn⟩ :=
      (hdiv.eventually_ge_atTop (1 + ∑ i ∈ Finset.range N, h i)).exists
    have hle : N ≤ max n N := le_max_right _ _
    refine ⟨max n N, ?_⟩
    have hmono : ∑ i ∈ Finset.range n, h i ≤
        ∑ i ∈ Finset.range (max n N), h i :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (le_max_left n N))
        fun i _ _ => (hpos i).le
    rw [Finset.sum_Ico_eq_sub h hle]
    linarith
  have hwindow : ∀ N : ℕ, ∃ k, N ≤ k ∧
      (∑ i ∈ Finset.Ico N k, h i) < 1 ∧
      1 ≤ (∑ i ∈ Finset.Ico N k, h i) + h k := by
    intro N
    have hex := hreach N
    have hspec : 1 ≤ ∑ i ∈ Finset.Ico N (Nat.find hex), h i := Nat.find_spec hex
    have hgt : N < Nat.find hex := by
      by_contra hcon
      rw [Finset.Ico_eq_empty_of_le (not_lt.mp hcon), Finset.sum_empty] at hspec
      norm_num at hspec
    have hk : N ≤ Nat.find hex - 1 := by omega
    have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    have hmin : ¬ (1 ≤ ∑ i ∈ Finset.Ico N (Nat.find hex - 1), h i) :=
      Nat.find_min hex (by omega)
    refine ⟨Nat.find hex - 1, hk, not_le.mp hmin, ?_⟩
    rw [← hsucc, Finset.sum_Ico_succ_top hk] at hspec
    exact hspec
  choose m hmN hmlt hmge using hwindow
  refine ⟨unitWindowProfile h m, ?_, ?_, ?_, ?_⟩
  · exact fun N n => unitWindowProfile_nonneg hpos hmlt N n
  · exact fun N n => unitWindowProfile_le_one hpos hmge N n
  · exact fun N => hasSum_unitWindowProfile_mass hpos hmN N
  · intro s
    filter_upwards [eventually_gt_atTop (s.sup id)] with N hN i hi
    exact unitWindowProfile_eq_zero_of_lt hmN
      (lt_of_le_of_lt (Finset.le_sup (f := id) hi) hN)

/-! ## Transport along a reindexing -/

/-- Reindexing a profile along an equivalence gives a profile for the reindexed
weight. -/
theorem IsCofinalUnitProfile.equivTransport {κ : Type*} (e : κ ≃ ι) {h : ι → ℝ}
    {nu : ℕ → κ → ℝ} (hnu : IsCofinalUnitProfile (fun k => h (e k)) nu) :
    IsCofinalUnitProfile h fun N i => nu N (e.symm i) := by
  classical
  refine ⟨fun N i => hnu.nonneg N _, fun N i => hnu.le_one N _, fun N => ?_,
    fun s => ?_⟩
  · refine (e.hasSum_iff (f := fun i => nu N (e.symm i) * h i)).mp ?_
    simpa [Function.comp_def] using hnu.hasSum_mass N
  · filter_upwards [hnu.escapes (s.image e.symm)] with N hN i hi
    exact hN _ (Finset.mem_image_of_mem _ hi)

/-- **Every divergent positive weight on a countable index set is read by a
bounded cofinal profile.** -/
theorem exists_isCofinalUnitProfile_of_equiv (e : ℕ ≃ ι) {h : ι → ℝ}
    (hpos : ∀ i, 0 < h i) (hns : ¬ Summable h) :
    ∃ mu : ℕ → ι → ℝ, IsCofinalUnitProfile h mu := by
  have hnsPull : ¬ Summable fun n => h (e n) := by
    intro hsum
    exact hns ((e.summable_iff (f := h)).mp (by simpa [Function.comp_def] using hsum))
  obtain ⟨nu, hnu⟩ :=
    exists_isCofinalUnitProfile (h := fun n => h (e n)) (fun n => hpos (e n)) hnsPull
  exact ⟨fun N i => nu N (e.symm i), hnu.equivTransport e⟩

/-! ## The prime-harmonic reference weight -/

/-- The prime-harmonic reference weight `p ↦ 1 / p`. -/
noncomputable def primeHarmonicWeight (p : Nat.Primes) : ℝ := ((p : ℕ) : ℝ)⁻¹

theorem primeHarmonicWeight_pos (p : Nat.Primes) : 0 < primeHarmonicWeight p := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  simpa [primeHarmonicWeight] using inv_pos.mpr hp

theorem not_summable_primeHarmonicWeight : ¬ Summable primeHarmonicWeight := by
  intro hsum
  refine Nat.Primes.not_summable_one_div (hsum.congr fun p => ?_)
  simp [primeHarmonicWeight, one_div]

/-- **The prime-harmonic residue is unique.**  Divergence of the prime
reciprocals alone forces it; no averaging construction is needed. -/
theorem primeHarmonicResidue_unique {a : Nat.Primes → ℂ} {c d : ℂ}
    (hc : HasReferenceResidue primeHarmonicWeight a c)
    (hd : HasReferenceResidue primeHarmonicWeight a d) : c = d :=
  HasReferenceResidue.unique not_summable_primeHarmonicWeight hc hd

/-- Bounded cofinal profiles reading the prime-harmonic weight exist. -/
theorem exists_isCofinalUnitProfile_primeHarmonic (e : ℕ ≃ Nat.Primes) :
    ∃ mu : ℕ → Nat.Primes → ℝ, IsCofinalUnitProfile primeHarmonicWeight mu :=
  exists_isCofinalUnitProfile_of_equiv e primeHarmonicWeight_pos
    not_summable_primeHarmonicWeight

end GaloisForLFunctions.HTGeometry
