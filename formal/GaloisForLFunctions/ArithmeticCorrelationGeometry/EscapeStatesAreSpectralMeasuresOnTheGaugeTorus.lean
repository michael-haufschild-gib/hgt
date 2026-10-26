import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction
import GaloisForLFunctions.ArithmeticPositiveDuality.HerglotzBochnerOnThePositiveRationals
import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter

/-!
# Escape states are spectral measures on the gauge torus

An escape state of the damped Möbius receiver (`ArithmeticDefectRigidity`) is a common limit `K` of
the cofactor Grams `K_T(j,k) = ⟨D_j A, D_k A⟩_T / E_T`, `D_j v(n) = v(⌊n/j⌋)`. Every such limit is
symmetric, positive semidefinite and **dilation contractive**:
`Σ c_j c_k K(pj, pk) ≤ (1/p) Σ c_j c_k K(j,k)`. This module reads it on the gauge torus.

* **Critical normalisation.** With `K̃(j,k) = √j √k K(j,k)` the dilation by `d` is a contraction of
  the quadratic form: the `d`-dilated forms `Q_d(c) = Σ c_j c_k K̃(dj, dk)` decrease along
  divisibility (`dilForm_le_of_eq_mul`) and stay nonnegative (`dilForm_nonneg`).
* **The asymptotic kernel** (`asymKernel`). Their infimum over all `d` is a limit along every
  divisibility chain cofinal in `ℕ_{>0}` (`tendsto_dilForm`); polarization gives a kernel `K̃_∞`,
  positive semidefinite (`asymKernel_form`) and **exactly dilation invariant**
  (`asymKernel_mul_mul`): the isometric part of the dilation action.
* **Spectral measure** (`exists_spectralMeasure`). `K̃_∞(j,k)` depends only on `j/k` and is positive
  definite on the group `ℚ_{>0}`; Herglotz–Bochner on `ℚ_{>0}`
  (`ArithmeticPositiveDuality.exists_measure_ratChar`) gives a unique finite measure `ν` on the
  prime torus with `K̃_∞(j,k) = ∫ χ_x(j/k) dν(x)`, of mass `K̃_∞(1,1) = inf_d d K(d,d) ≤ K(1,1)`.
* **Gauge invariance** (`spectralMeasure_eq_haar_iff`). `ν` is a multiple of Haar measure exactly
  when `K̃_∞` is diagonal.
* **Escape states** (`exists_actualCofactorLimit_spectralMeasure`). Every actual cofactor limit has
  a spectral measure of mass at most one. An exactly covariant kernel `K(pj,pk) = K(j,k)/p`
  (the full-horizon receiver Gram) is its own asymptotic kernel (`asymKernel_eq_of_covariant`).

Gauge status: the escape state is a measure on the gauge torus, not a gauge point. It is gauge
invariant only when its dilated rows become orthogonal; any off-diagonal asymptotic correlation of
dilated receivers is a non-Haar spectral component, i.e. arithmetic information that a single
twist can carry.
-/

open MeasureTheory Finset Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open ArithmeticPositiveDuality HTGeometry

/-! ### Reindexing packets -/

/-- A packet over an arbitrary index map is a packet over its image with fibre-summed weights. -/
theorem sum_sum_comp {ι : Type*} [DecidableEq ι] (F : ℕ+ → ℕ+ → ℝ) (S : Finset ι) (c : ι → ℝ)
    (a : ι → ℕ+) :
    ∑ i ∈ S, ∑ i' ∈ S, c i * c i' * F (a i) (a i') =
      ∑ m ∈ S.image a, ∑ m' ∈ S.image a,
        (∑ i ∈ S with a i = m, c i) * (∑ i ∈ S with a i = m', c i) * F m m' := by
  have hmaps : ∀ i ∈ S, a i ∈ S.image a := fun i hi => mem_image_of_mem a hi
  have hinner : ∀ m : ℕ+, ∑ i' ∈ S, c i' * F m (a i') =
      ∑ m' ∈ S.image a, (∑ i ∈ S with a i = m', c i) * F m m' := by
    intro m
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun m' _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [(mem_filter.mp hi).2]
  calc ∑ i ∈ S, ∑ i' ∈ S, c i * c i' * F (a i) (a i')
      = ∑ i ∈ S, c i * ∑ i' ∈ S, c i' * F (a i) (a i') := by
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun i' _ => by ring
    _ = ∑ m ∈ S.image a, ∑ i ∈ S with a i = m, c i * ∑ i' ∈ S, c i' * F m (a i') := by
        rw [← sum_fiberwise_of_maps_to hmaps]
        refine sum_congr rfl fun m _ => sum_congr rfl fun i hi => ?_
        rw [(mem_filter.mp hi).2]
    _ = _ := by
        refine sum_congr rfl fun m _ => ?_
        rw [← sum_mul, hinner, mul_sum]
        exact sum_congr rfl fun m' _ => by ring

variable {K : ℕ+ → ℕ+ → ℝ}

theorem psd_comp (hpsd : ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ), 0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℝ) (a : ι → ℕ+) :
    0 ≤ ∑ i ∈ S, ∑ i' ∈ S, c i * c i' * K (a i) (a i') := by
  rw [sum_sum_comp]
  exact hpsd _ _

theorem contr_comp (hcontr : ∀ (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ),
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * K (p * j) (p * k) ≤
        (1 / (p : ℝ)) * ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
    (p : ℕ+) {ι : Type*} [DecidableEq ι] (S : Finset ι) (c : ι → ℝ) (a : ι → ℕ+) :
    ∑ i ∈ S, ∑ i' ∈ S, c i * c i' * K (p * a i) (p * a i') ≤
      (1 / (p : ℝ)) * ∑ i ∈ S, ∑ i' ∈ S, c i * c i' * K (a i) (a i') := by
  have h1 : ∑ i ∈ S, ∑ i' ∈ S, c i * c i' * K (p * a i) (p * a i') =
      ∑ m ∈ S.image a, ∑ m' ∈ S.image a, (∑ i ∈ S with a i = m, c i) *
        (∑ i ∈ S with a i = m', c i) * K (p * m) (p * m') :=
    sum_sum_comp (fun m m' => K (p * m) (p * m')) S c a
  have h2 : ∑ i ∈ S, ∑ i' ∈ S, c i * c i' * K (a i) (a i') =
      ∑ m ∈ S.image a, ∑ m' ∈ S.image a, (∑ i ∈ S with a i = m, c i) *
        (∑ i ∈ S with a i = m', c i) * K m m' := sum_sum_comp K S c a
  rw [h1, h2]
  exact hcontr p _ _

/-! ### The critically normalised dilated forms -/

variable (K) in
/-- The critically normalised kernel `√j √k K(j,k)`. -/
def critKernel (j k : ℕ+) : ℝ := Real.sqrt j * Real.sqrt k * K j k

variable (K) in
/-- The `d`-dilated critical form `Σ c_j c_k √(dj) √(dk) K(dj, dk)`. -/
def dilForm (d : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) : ℝ :=
  ∑ j ∈ S, ∑ k ∈ S, c j * c k * critKernel K (d * j) (d * k)

theorem dilForm_eq (d : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    dilForm K d S c = ∑ j ∈ S, ∑ k ∈ S, (c j * Real.sqrt ((d * j : ℕ+) : ℝ)) *
      (c k * Real.sqrt ((d * k : ℕ+) : ℝ)) * K (d * j) (d * k) := by
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [critKernel]
  ring

theorem dilForm_nonneg (hpsd : ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ),
      0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k) (d : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ dilForm K d S c := by
  rw [dilForm_eq]
  exact psd_comp hpsd S (fun j => c j * Real.sqrt ((d * j : ℕ+) : ℝ)) (fun j => d * j)

/-- **Dilation contracts the critical form**: `Q_{de} ≤ Q_d`. -/
theorem dilForm_mul_le (hcontr : ∀ (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ),
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * K (p * j) (p * k) ≤
        (1 / (p : ℝ)) * ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
    (d e : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    dilForm K (d * e) S c ≤ dilForm K d S c := by
  have he : (0 : ℝ) < e := by exact_mod_cast e.pos
  have hsplit : dilForm K (d * e) S c = (e : ℝ) * ∑ j ∈ S, ∑ k ∈ S,
      (c j * Real.sqrt ((d * j : ℕ+) : ℝ)) * (c k * Real.sqrt ((d * k : ℕ+) : ℝ)) *
        K (e * (d * j)) (e * (d * k)) := by
    rw [dilForm, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    have hj : ((d * e * j : ℕ+) : ℝ) = (e : ℝ) * ((d * j : ℕ+) : ℝ) := by push_cast; ring
    have hk : ((d * e * k : ℕ+) : ℝ) = (e : ℝ) * ((d * k : ℕ+) : ℝ) := by push_cast; ring
    have hej : e * (d * j) = d * e * j := by rw [mul_comm d e, mul_assoc]
    have hek : e * (d * k) = d * e * k := by rw [mul_comm d e, mul_assoc]
    rw [critKernel, hj, hk, Real.sqrt_mul he.le, Real.sqrt_mul he.le, hej, hek]
    have := Real.mul_self_sqrt he.le
    linear_combination (c j * c k * Real.sqrt ((d * j : ℕ+) : ℝ) * Real.sqrt ((d * k : ℕ+) : ℝ) *
      K (d * e * j) (d * e * k)) * this
  rw [hsplit, dilForm_eq]
  calc (e : ℝ) * ∑ j ∈ S, ∑ k ∈ S, (c j * Real.sqrt ((d * j : ℕ+) : ℝ)) *
        (c k * Real.sqrt ((d * k : ℕ+) : ℝ)) * K (e * (d * j)) (e * (d * k))
      ≤ (e : ℝ) * ((1 / (e : ℝ)) * ∑ j ∈ S, ∑ k ∈ S, (c j * Real.sqrt ((d * j : ℕ+) : ℝ)) *
        (c k * Real.sqrt ((d * k : ℕ+) : ℝ)) * K (d * j) (d * k)) :=
        mul_le_mul_of_nonneg_left (contr_comp hcontr e S
          (fun j => c j * Real.sqrt ((d * j : ℕ+) : ℝ)) fun j => d * j) he.le
    _ = _ := by field_simp

theorem dilForm_le_of_eq_mul (hcontr : ∀ (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ),
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * K (p * j) (p * k) ≤
        (1 / (p : ℝ)) * ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
    {d d' : ℕ+} (h : ∃ e, d' = d * e) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    dilForm K d' S c ≤ dilForm K d S c := by
  obtain ⟨e, rfl⟩ := h
  exact dilForm_mul_le hcontr d e S c

/-! ### The asymptotic kernel -/

variable (K) in
/-- The asymptotic critical form: the infimum of the dilated forms. -/
def asymForm (S : Finset ℕ+) (c : ℕ+ → ℝ) : ℝ := ⨅ d : ℕ+, dilForm K d S c

/-- A divisibility chain cofinal in `ℕ_{>0}`. -/
def IsCofinalChain (e : ℕ → ℕ+) : Prop :=
  (∀ n, ∃ m, e (n + 1) = e n * m) ∧ ∀ d : ℕ+, ∃ n m, e n = d * m

section Limits

variable (hpsd : ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ), 0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
  (hcontr : ∀ (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ),
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * K (p * j) (p * k) ≤
        (1 / (p : ℝ)) * ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
include hpsd hcontr

omit hcontr in
theorem bddBelow_dilForm (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    BddBelow (Set.range fun d : ℕ+ => dilForm K d S c) :=
  ⟨0, by rintro _ ⟨d, rfl⟩; exact dilForm_nonneg hpsd d S c⟩

/-- **The dilated forms converge along every cofinal divisibility chain** to their infimum. -/
theorem tendsto_dilForm {e : ℕ → ℕ+} (he : IsCofinalChain e) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    Tendsto (fun n => dilForm K (e n) S c) atTop (𝓝 (asymForm K S c)) := by
  have hchain : ∀ n m, n ≤ m → ∃ r, e m = e n * r := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨1, (mul_one _).symm⟩
    | succ m _ ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨s, hs⟩ := he.1 m
      exact ⟨r * s, by rw [hs, hr, mul_assoc]⟩
  have hanti : Antitone fun n => dilForm K (e n) S c := fun n m hnm =>
    dilForm_le_of_eq_mul hcontr (hchain n m hnm) S c
  have hbdd : BddBelow (Set.range fun n => dilForm K (e n) S c) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact dilForm_nonneg hpsd _ S c⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have heq : (⨅ n, dilForm K (e n) S c) = asymForm K S c := by
    refine le_antisymm (le_ciInf fun d => ?_) (le_ciInf fun n => ciInf_le (bddBelow_dilForm hpsd S c) _)
    obtain ⟨n, m, hnm⟩ := he.2 d
    exact (ciInf_le hbdd n).trans (dilForm_le_of_eq_mul hcontr ⟨m, hnm⟩ S c)
  rwa [heq] at hlim

omit hcontr in
theorem asymForm_nonneg (S : Finset ℕ+) (c : ℕ+ → ℝ) : 0 ≤ asymForm K S c :=
  le_ciInf fun d => dilForm_nonneg hpsd d S c

end Limits

/-- The factorial chain `(n+1)!`. -/
def facChain (n : ℕ) : ℕ+ := ⟨(n + 1).factorial, Nat.factorial_pos _⟩

theorem isCofinalChain_mul_facChain (p : ℕ+) : IsCofinalChain fun n => p * facChain n := by
  refine ⟨fun n => ⟨⟨n + 2, by omega⟩, ?_⟩, fun d => ⟨(d : ℕ) - 1, p * ⟨((d : ℕ) - 1).factorial,
    Nat.factorial_pos _⟩, ?_⟩⟩
  · apply PNat.eq
    simp only [facChain, PNat.mul_coe, PNat.mk_coe]
    rw [show n + 1 + 1 = n + 2 by ring, Nat.factorial_succ (n + 1)]
    ring
  · apply PNat.eq
    simp only [facChain, PNat.mul_coe, PNat.mk_coe]
    have hd : (d : ℕ) - 1 + 1 = d := Nat.sub_add_cancel d.pos
    rw [hd]
    conv_lhs => rw [← hd, Nat.factorial_succ, hd]
    ring

theorem isCofinalChain_facChain : IsCofinalChain facChain := by
  have := isCofinalChain_mul_facChain 1
  simpa using this

variable (K) in
/-- The asymptotic kernel `K̃_∞(j,k)`, by polarization of the asymptotic form on `{j, k}`. -/
def asymKernel (j k : ℕ+) : ℝ :=
  (asymForm K {j, k} (fun i => (if i = j then 1 else 0) + (if i = k then 1 else 0)) -
    asymForm K {j, k} (fun i => (if i = j then 1 else 0) - (if i = k then 1 else 0))) / 4

/-- Polarization of a dilated form. -/
theorem critKernel_eq_polarization (hsymm : ∀ j k, K j k = K k j) (d j k : ℕ+) :
    critKernel K (d * j) (d * k) =
      (dilForm K d {j, k} (fun i => (if i = j then 1 else 0) + (if i = k then 1 else 0)) -
        dilForm K d {j, k} (fun i => (if i = j then 1 else 0) - (if i = k then 1 else 0))) / 4 := by
  have hcs : critKernel K (d * k) (d * j) = critKernel K (d * j) (d * k) := by
    rw [critKernel, critKernel, hsymm]; ring
  by_cases hjk : j = k
  · subst hjk
    simp [dilForm]
    ring
  · simp only [dilForm, sum_pair hjk, if_neg hjk, if_neg (Ne.symm hjk), if_true]
    rw [hcs]
    ring

/-- The numerator of a positive rational, as a positive integer. -/
def posNum (u : posUnits) : ℕ+ :=
  ⟨((u : ℚˣ) : ℚ).num.toNat, by
    have : 0 < ((u : ℚˣ) : ℚ).num := Rat.num_pos.mpr u.2
    omega⟩

/-- The denominator of a positive rational, as a positive integer. -/
def posDen (u : posUnits) : ℕ+ := ⟨((u : ℚˣ) : ℚ).den, ((u : ℚˣ) : ℚ).den_pos⟩

theorem posNum_div_posDen (u : posUnits) :
    ((posNum u : ℕ) : ℚ) / ((posDen u : ℕ) : ℚ) = ((u : ℚˣ) : ℚ) := by
  have hnum : 0 < ((u : ℚˣ) : ℚ).num := Rat.num_pos.mpr u.2
  simp only [posNum, posDen, PNat.mk_coe]
  rw [show (((((u : ℚˣ) : ℚ).num.toNat : ℕ) : ℚ)) = (((u : ℚˣ) : ℚ).num : ℚ) by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]]
  exact Rat.num_div_den _

/-- The positive rational `j/k` as an element of `ℚ_{>0}`. -/
def ratUnit (j k : ℕ+) : posUnits :=
  ⟨Units.mk0 ((j : ℚ) / (k : ℚ)) (div_ne_zero (by exact_mod_cast j.ne_zero)
    (by exact_mod_cast k.ne_zero)), by
    show (0 : ℚ) < (j : ℚ) / (k : ℚ)
    exact div_pos (by exact_mod_cast j.pos) (by exact_mod_cast k.pos)⟩

/-- `j/k` has trivial valuation vector only when `j = k`. -/
theorem valFinsupp_div_ne_zero {j k : ℕ+} (hjk : j ≠ k) : valFinsupp ((j : ℚ) / (k : ℚ)) ≠ 0 := by
  intro h0
  have hv : valFinsupp (((ratUnit j k : posUnits) : ℚˣ) : ℚ) = 0 := h0
  have : ratUnit j k = 1 := by
    rw [← finsuppUnit_valFinsupp (ratUnit j k), hv]
    simp [finsuppUnit]
  have hq := congrArg (fun u : posUnits => ((u : ℚˣ) : ℚ)) this
  simp only [ratUnit, Units.val_mk0, OneMemClass.coe_one, Units.val_one] at hq
  have hk : ((k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast k.ne_zero
  rw [div_eq_one_iff_eq hk] at hq
  exact hjk (PNat.eq (by exact_mod_cast hq))

section Kernel

variable (hsymm : ∀ j k, K j k = K k j)
  (hpsd : ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ), 0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
  (hcontr : ∀ (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ),
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * K (p * j) (p * k) ≤
        (1 / (p : ℝ)) * ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
include hsymm hpsd hcontr

/-- **The dilated critical kernel converges** along every cofinal chain to `K̃_∞`. -/
theorem tendsto_critKernel {e : ℕ → ℕ+} (he : IsCofinalChain e) (j k : ℕ+) :
    Tendsto (fun n => critKernel K (e n * j) (e n * k)) atTop (𝓝 (asymKernel K j k)) := by
  simp_rw [critKernel_eq_polarization hsymm]
  exact ((tendsto_dilForm hpsd hcontr he _ _).sub (tendsto_dilForm hpsd hcontr he _ _)).div_const 4

/-- The asymptotic form is the form of the asymptotic kernel. -/
theorem asymKernel_form (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    ∑ j ∈ S, ∑ k ∈ S, c j * c k * asymKernel K j k = asymForm K S c := by
  have h1 : Tendsto (fun n => dilForm K (facChain n) S c) atTop
      (𝓝 (∑ j ∈ S, ∑ k ∈ S, c j * c k * asymKernel K j k)) :=
    tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ =>
      tendsto_const_nhds.mul (tendsto_critKernel hsymm hpsd hcontr isCofinalChain_facChain j k)
  exact tendsto_nhds_unique h1 (tendsto_dilForm hpsd hcontr isCofinalChain_facChain S c)

theorem asymKernel_psd (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * asymKernel K j k := by
  rw [asymKernel_form hsymm hpsd hcontr]
  exact asymForm_nonneg hpsd S c

theorem asymKernel_symm (j k : ℕ+) : asymKernel K j k = asymKernel K k j := by
  refine tendsto_nhds_unique (tendsto_critKernel hsymm hpsd hcontr isCofinalChain_facChain j k) ?_
  refine (tendsto_critKernel hsymm hpsd hcontr isCofinalChain_facChain k j).congr fun n => ?_
  rw [critKernel, critKernel, hsymm]
  ring

/-- **The asymptotic kernel is exactly dilation invariant.** -/
theorem asymKernel_mul_mul (p j k : ℕ+) : asymKernel K (p * j) (p * k) = asymKernel K j k := by
  refine tendsto_nhds_unique (tendsto_critKernel hsymm hpsd hcontr isCofinalChain_facChain _ _) ?_
  refine (tendsto_critKernel hsymm hpsd hcontr (isCofinalChain_mul_facChain p) j k).congr fun n => ?_
  rw [mul_comm p (facChain n), mul_assoc, mul_assoc]

/-- The mass of the asymptotic kernel is at most `K(1,1)`. -/
theorem asymKernel_one_one_le : asymKernel K 1 1 ≤ K 1 1 := by
  have h := asymKernel_form hsymm hpsd hcontr {1} fun _ => 1
  simp only [sum_singleton, mul_one, one_mul] at h
  rw [h]
  refine (ciInf_le (bddBelow_dilForm hpsd _ _) 1).trans_eq ?_
  simp [dilForm, critKernel]

/-! ### The ratio function and its spectral measure -/

variable (K) in
/-- The ratio function `u ↦ K̃_∞(num u, den u)` on `ℚ_{>0}`. -/
def ratioFunction (u : posUnits) : ℂ := (asymKernel K (posNum u) (posDen u) : ℂ)

/-- The ratio function reads `K̃_∞(j,k)` at every representation `u = j/k`. -/
theorem ratioFunction_eq (u : posUnits) (j k : ℕ+)
    (h : ((u : ℚˣ) : ℚ) = (j : ℚ) / (k : ℚ)) :
    ratioFunction K u = (asymKernel K j k : ℂ) := by
  rw [ratioFunction]
  congr 1
  have hcross : (posNum u : ℕ) * (k : ℕ) = (posDen u : ℕ) * (j : ℕ) := by
    have h2 := posNum_div_posDen u
    rw [h] at h2
    have hk : ((k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hd : ((posDen u : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (posDen u).ne_zero
    field_simp at h2
    exact_mod_cast h2
  have hpk : k * posNum u = posDen u * j := by
    apply PNat.eq; simp only [PNat.mul_coe]; rw [mul_comm, hcross]
  rw [← asymKernel_mul_mul hsymm hpsd hcontr k, hpk, mul_comm k (posDen u),
    asymKernel_mul_mul hsymm hpsd hcontr]

/-- **The ratio function is positive definite on `ℚ_{>0}`.** -/
theorem isPosDefOnGroup_ratioFunction : IsPosDefOnGroup (ratioFunction K) := by
  classical
  intro N x c
  -- common denominators
  set D : ℕ → ℕ := fun a => if h : a < N then (posDen (x ⟨a, h⟩) : ℕ) else 1
  let n : Fin N → ℕ+ := fun a => posNum (x a) * ∏ b ∈ univ.erase a, posDen (x b)
  have hval : ∀ a, ((n a : ℕ) : ℚ) = ((x a : ℚˣ) : ℚ) * ∏ b, ((posDen (x b) : ℕ) : ℚ) := by
    intro a
    rw [← mul_prod_erase univ (fun b => ((posDen (x b) : ℕ) : ℚ)) (mem_univ a),
      ← posNum_div_posDen (x a)]
    have hd : ((posDen (x a) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (posDen (x a)).ne_zero
    simp only [n, PNat.mul_coe, Nat.cast_mul, PNat.coe_prod, Nat.cast_prod]
    field_simp
  have hratio : ∀ a b, ratioFunction K ((x a)⁻¹ * x b) = (asymKernel K (n b) (n a) : ℂ) := by
    intro a b
    refine ratioFunction_eq hsymm hpsd hcontr _ _ _ ?_
    have hP : (∏ b, ((posDen (x b) : ℕ) : ℚ)) ≠ 0 :=
      prod_ne_zero_iff.mpr fun b _ => by exact_mod_cast (posDen (x b)).ne_zero
    have hxa : ((x a : ℚˣ) : ℚ) ≠ 0 := (x a : ℚˣ).ne_zero
    rw [hval, hval]
    push_cast
    field_simp
  set L : Fin N → Fin N → ℝ := fun a b => asymKernel K (n a) (n b)
  have hLsymm : ∀ a b, L a b = L b a := fun a b => asymKernel_symm hsymm hpsd hcontr _ _
  have hLpsd : ∀ w : Fin N → ℝ, 0 ≤ ∑ a, ∑ b, w a * w b * L a b := fun w =>
    psd_comp (asymKernel_psd hsymm hpsd hcontr) univ w n
  refine ⟨∑ a, ∑ b, (c a).re * (c b).re * L a b + ∑ a, ∑ b, (c a).im * (c b).im * L a b,
    add_nonneg (hLpsd _) (hLpsd _), ?_⟩
  simp_rw [hratio]
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.ofReal_re]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, L]
    rw [asymKernel_symm hsymm hpsd hcontr (n b) (n a)]
    ring
  · simp only [Complex.im_sum, Complex.ofReal_im]
    have hterm : ∀ a b, (star (c a) * (asymKernel K (n b) (n a) : ℂ) * c b).im =
        L a b * ((c a).re * (c b).im) - L b a * ((c b).re * (c a).im) := by
      intro a b
      simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, L]
      rw [asymKernel_symm hsymm hpsd hcontr (n b) (n a), asymKernel_symm hsymm hpsd hcontr (n a) (n b)]
      ring
    simp_rw [hterm, sum_sub_distrib]
    rw [sum_comm (f := fun a b => L b a * ((c b).re * (c a).im))]
    ring

/-- **Every dilation-contractive positive kernel has a spectral measure on the gauge torus.** There
is a finite measure `ν` on the prime torus with `K̃_∞(j,k) = ∫ χ_x(j/k) dν(x)` for all `j, k`. -/
theorem exists_spectralMeasure :
    ∃ ν : Measure ArithmeticPositiveDuality.PrimeTorus, IsFiniteMeasure ν ∧
      ∀ j k : ℕ+, ∫ x, ratChar ((j : ℚ) / (k : ℚ)) x ∂ν = (asymKernel K j k : ℂ) := by
  obtain ⟨ν, hν, hrep⟩ := exists_measure_ratChar (isPosDefOnGroup_ratioFunction hsymm hpsd hcontr)
  refine ⟨ν, hν, fun j k => ?_⟩
  have := hrep (ratUnit j k)
  rw [ratioFunction_eq hsymm hpsd hcontr (ratUnit j k) j k rfl] at this
  exact this.symm

omit hsymm hpsd hcontr in
/-- **Gauge invariance of the spectral measure.** A spectral measure of `K̃_∞` is a multiple of Haar
measure on the prime torus exactly when `K̃_∞` is diagonal. -/
theorem spectralMeasure_eq_haar_iff {ν : Measure ArithmeticPositiveDuality.PrimeTorus} [IsFiniteMeasure ν]
    (hν : ∀ j k : ℕ+, ∫ x, ratChar ((j : ℚ) / (k : ℚ)) x ∂ν = (asymKernel K j k : ℂ)) :
    ν = ν Set.univ • torusHaar Nat.Primes ↔ ∀ j k : ℕ+, j ≠ k → asymKernel K j k = 0 := by
  classical
  have hHaar : ∀ q : ℚ, ∫ x, ratChar q x ∂(torusHaar Nat.Primes) =
      if valFinsupp q = 0 then 1 else 0 := fun q => by
    rw [show (fun x => ratChar q x) = fun x => torusCharacter (valFinsupp q) x from rfl,
      integral_torusCharacter]
  constructor
  · intro h j k hjk
    have := hν j k
    rw [h, integral_smul_measure, hHaar, if_neg (valFinsupp_div_ne_zero hjk), smul_zero] at this
    exact_mod_cast this.symm
  · intro hdiag
    haveI : IsFiniteMeasure (ν Set.univ • torusHaar Nat.Primes) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, measure_univ (μ := torusHaar Nat.Primes), mul_one]
          exact measure_lt_top ν _⟩
    refine finiteMeasure_ext_of_ratChar fun u => ?_
    rw [integral_smul_measure, hHaar]
    obtain ⟨j, k, hjk⟩ : ∃ j k : ℕ+, ((u : ℚˣ) : ℚ) = (j : ℚ) / (k : ℚ) :=
      ⟨posNum u, posDen u, (posNum_div_posDen u).symm⟩
    rw [hjk, hν]
    by_cases h : j = k
    · subst h
      have hk : ((j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast j.ne_zero
      have hv : valFinsupp ((j : ℚ) / (j : ℚ)) = 0 := by rw [div_self hk]; ext p; simp
      rw [if_pos hv]
      have hm := hν j j
      rw [div_self hk] at hm
      simp only [ratChar_one, integral_const] at hm
      rw [← hm, measureReal_def]
    · rw [if_neg (valFinsupp_div_ne_zero h), hdiag j k h, smul_zero]; rfl

/-- **Exactly covariant kernels are their own asymptotic kernels.** If `K(pj, pk) = K(j,k)/p`, then
`K̃_∞ = K̃`. -/
theorem asymKernel_eq_of_covariant (hcov : ∀ p j k : ℕ+, K (p * j) (p * k) = K j k / p)
    (j k : ℕ+) : asymKernel K j k = critKernel K j k := by
  have hc : ∀ d : ℕ+, critKernel K (d * j) (d * k) = critKernel K j k := by
    intro d
    have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
    rw [critKernel, critKernel, hcov]
    push_cast
    rw [Real.sqrt_mul hd.le, Real.sqrt_mul hd.le]
    field_simp
    rw [Real.sq_sqrt hd.le]
    ring
  refine tendsto_nhds_unique (tendsto_critKernel hsymm hpsd hcontr isCofinalChain_facChain j k) ?_
  simp_rw [hc]
  exact tendsto_const_nhds

end Kernel

/-! ### Escape states of the damped Möbius receiver -/

/-- **Every escape state is a spectral measure on the gauge torus.** Each actual cofactor limit `L`
has a finite measure `ν` on the prime torus with `K̃_∞(j,k) = ∫ χ_x(j/k) dν`, of mass at most one. -/
theorem exists_actualCofactorLimit_spectralMeasure {ε : ArithmeticDefectRigidity.SubcriticalDamping}
    (L : ArithmeticDefectRigidity.ActualCofactorLimit ε) :
    ∃ ν : Measure ArithmeticPositiveDuality.PrimeTorus, IsFiniteMeasure ν ∧
      (∀ j k : ℕ+, ∫ x, ratChar ((j : ℚ) / (k : ℚ)) x ∂ν = (asymKernel L.kernel j k : ℂ)) ∧
      asymKernel L.kernel 1 1 ≤ 1 := by
  have hsymm := L.kernel_symm
  have hpsd := L.packet_nonneg
  have hcontr := L.packet_dilation_le
  obtain ⟨ν, hν, hrep⟩ := exists_spectralMeasure hsymm hpsd hcontr
  refine ⟨ν, hν, hrep, ?_⟩
  have := asymKernel_one_one_le hsymm hpsd hcontr
  rwa [L.kernel_one_one] at this

end GaloisForLFunctions.ArithmeticCorrelationGeometry
