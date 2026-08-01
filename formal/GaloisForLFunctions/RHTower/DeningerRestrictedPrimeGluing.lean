import GaloisForLFunctions.RHTower.DeningerRestrictedPrimeSheaf
import GaloisForLFunctions.RHTower.DeningerBasisAmplitude
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# The restricted prime sum is a sheaf on the arithmetic base

Sections over an arithmetic open are the prime-indexed families supported on the primes of that
open which satisfy the two weighted summability conditions, one for each seminorm.  These form a
module: the seminorm axioms turn the two conditions into comparison estimates.

Restriction is coordinate deletion.  Gluing works because the arithmetic base is a Noetherian
space, so every open is quasi-compact: an arbitrary cover reduces to a finite one, and the glued
family is dominated by the finite sum of the covering families.  Uniqueness is coordinatewise.
This is the unique-gluing form of the sheaf axiom.

Flasqueness is extension by zero: it preserves both conditions and is a section of the deletion.

* `deningerPrimeSections` : the sections over an arithmetic open.
* `deningerPrimeSections_unique_gluing` : the sheaf axiom.
* `deningerPrimeSections_restrict_surjective` : flasqueness.
-/

namespace RHTower

open TopologicalSpace

section PrimeSections

variable {E : Nat.Primes → Type*} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
variable (n1 n2 : ∀ p, Seminorm ℝ (E p)) (α β : Nat.Primes → NNReal)

/-- The closed point of the arithmetic base attached to a prime. -/
def deningerPrimeSpectrumPoint (p : Nat.Primes) : PrimeSpectrum ℤ :=
  deningerClosedPoint ((p : ℕ) : ℤ) (Nat.prime_iff_prime_int.mp p.2)

/-- The primes of an arithmetic open. -/
def deningerPrimeIndex (U : Opens (PrimeSpectrum ℤ)) : Set Nat.Primes :=
  {p | deningerPrimeSpectrumPoint p ∈ U}

theorem deningerPrimeIndex_mono {U V : Opens (PrimeSpectrum ℤ)} (h : V ≤ U) :
    deningerPrimeIndex V ⊆ deningerPrimeIndex U := fun _ hp => h hp

theorem deningerMem_primeIndex_iSup {ι : Type*} {U : ι → Opens (PrimeSpectrum ℤ)}
    {p : Nat.Primes} : p ∈ deningerPrimeIndex (iSup U) ↔ ∃ i, p ∈ deningerPrimeIndex (U i) :=
  Opens.mem_iSup

/-- **The sections of the restricted prime sum over an arithmetic open**: families supported on the
primes of the open, with both weighted sums finite. -/
def deningerPrimeSections (U : Opens (PrimeSpectrum ℤ)) : Submodule ℝ (∀ p, E p) where
  carrier :=
    {f | (∀ p, p ∉ deningerPrimeIndex U → f p = 0)
      ∧ Summable (fun p => (α p : ℝ) * n1 p (f p))
      ∧ Summable (fun p => (β p : ℝ) * (n2 p (f p)) ^ 2)}
  zero_mem' := by
    refine ⟨fun p _ => rfl, ?_, ?_⟩
    · simp
    · simp
  add_mem' := by
    rintro f g ⟨hf0, hf1, hf2⟩ ⟨hg0, hg1, hg2⟩
    refine ⟨fun p hp => by rw [Pi.add_apply, hf0 p hp, hg0 p hp, add_zero], ?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hf1.add hg1)
      · exact mul_nonneg (α p).coe_nonneg (apply_nonneg _ _)
      · show (α p : ℝ) * n1 p (f p + g p) ≤ (α p : ℝ) * n1 p (f p) + (α p : ℝ) * n1 p (g p)
        have hsub : n1 p (f p + g p) ≤ n1 p (f p) + n1 p (g p) := map_add_le_add _ _ _
        have hα : (0 : ℝ) ≤ (α p : ℝ) := (α p).coe_nonneg
        nlinarith [apply_nonneg (n1 p) (f p), apply_nonneg (n1 p) (g p)]
    · refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
        ((hf2.mul_left 2).add (hg2.mul_left 2))
      · exact mul_nonneg (β p).coe_nonneg (by positivity)
      · show (β p : ℝ) * (n2 p (f p + g p)) ^ 2
            ≤ 2 * ((β p : ℝ) * (n2 p (f p)) ^ 2) + 2 * ((β p : ℝ) * (n2 p (g p)) ^ 2)
        have hsub : n2 p (f p + g p) ≤ n2 p (f p) + n2 p (g p) := map_add_le_add _ _ _
        have hβ : (0 : ℝ) ≤ (β p : ℝ) := (β p).coe_nonneg
        have hfn := apply_nonneg (n2 p) (f p)
        have hgn := apply_nonneg (n2 p) (g p)
        have hsq : (n2 p (f p + g p)) ^ 2 ≤ 2 * (n2 p (f p)) ^ 2 + 2 * (n2 p (g p)) ^ 2 := by
          nlinarith [apply_nonneg (n2 p) (f p + g p), sq_nonneg (n2 p (f p) - n2 p (g p))]
        nlinarith
  smul_mem' := by
    rintro c f ⟨hf0, hf1, hf2⟩
    refine ⟨fun p hp => by rw [Pi.smul_apply, hf0 p hp, smul_zero], ?_, ?_⟩
    · refine Summable.congr (hf1.mul_left |c|) fun p => ?_
      show |c| * ((α p : ℝ) * n1 p (f p)) = (α p : ℝ) * n1 p (c • f p)
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      ring
    · refine Summable.congr (hf2.mul_left (|c| ^ 2)) fun p => ?_
      show |c| ^ 2 * ((β p : ℝ) * (n2 p (f p)) ^ 2) = (β p : ℝ) * (n2 p (c • f p)) ^ 2
      rw [map_smul_eq_mul, Real.norm_eq_abs]
      ring

variable {n1 n2 α β}

theorem deningerMem_primeSections {U : Opens (PrimeSpectrum ℤ)} {f : ∀ p, E p} :
    f ∈ deningerPrimeSections n1 n2 α β U ↔
      (∀ p, p ∉ deningerPrimeIndex U → f p = 0)
        ∧ Summable (fun p => (α p : ℝ) * n1 p (f p))
        ∧ Summable (fun p => (β p : ℝ) * (n2 p (f p)) ^ 2) := Iff.rfl

/-- Coordinate deletion: the restriction of a family to the primes of a smaller open. -/
noncomputable def deningerPrimeRestrict (V : Opens (PrimeSpectrum ℤ)) (f : ∀ p, E p)
    (p : Nat.Primes) : E p :=
  open Classical in
  if p ∈ deningerPrimeIndex V then f p else 0

omit [∀ p, Module ℝ (E p)] in
theorem deningerPrimeRestrict_of_mem {V : Opens (PrimeSpectrum ℤ)} {f : ∀ p, E p} {p : Nat.Primes}
    (hp : p ∈ deningerPrimeIndex V) : deningerPrimeRestrict V f p = f p := by
  classical
  exact if_pos hp

omit [∀ p, Module ℝ (E p)] in
theorem deningerPrimeRestrict_of_notMem {V : Opens (PrimeSpectrum ℤ)} {f : ∀ p, E p}
    {p : Nat.Primes} (hp : p ∉ deningerPrimeIndex V) : deningerPrimeRestrict V f p = 0 := by
  classical
  exact if_neg hp

/-- **Restriction lands in the sections of the smaller open.** -/
theorem deningerPrimeRestrict_mem {U V : Opens (PrimeSpectrum ℤ)} {f : ∀ p, E p}
    (hf : f ∈ deningerPrimeSections n1 n2 α β U) :
    deningerPrimeRestrict V f ∈ deningerPrimeSections n1 n2 α β V := by
  obtain ⟨_, hf1, hf2⟩ := hf
  refine ⟨fun p hp => deningerPrimeRestrict_of_notMem hp, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun p => mul_nonneg (α p).coe_nonneg (apply_nonneg _ _))
      (fun p => ?_) hf1
    by_cases hp : p ∈ deningerPrimeIndex V
    · rw [deningerPrimeRestrict_of_mem hp]
    · rw [deningerPrimeRestrict_of_notMem hp, map_zero, mul_zero]
      exact mul_nonneg (α p).coe_nonneg (apply_nonneg _ _)
  · refine Summable.of_nonneg_of_le (fun p => mul_nonneg (β p).coe_nonneg (by positivity))
      (fun p => ?_) hf2
    by_cases hp : p ∈ deningerPrimeIndex V
    · rw [deningerPrimeRestrict_of_mem hp]
    · rw [deningerPrimeRestrict_of_notMem hp, map_zero]
      have hz : ((0 : ℝ)) ^ 2 = 0 := by norm_num
      rw [hz, mul_zero]
      exact mul_nonneg (β p).coe_nonneg (by positivity)

/-- **Flasqueness.**  Every section over a smaller open is the restriction of a section over the
bigger one: extension by zero preserves both conditions. -/
theorem deningerPrimeSections_restrict_surjective {U V : Opens (PrimeSpectrum ℤ)} (hVU : V ≤ U)
    {g : ∀ p, E p} (hg : g ∈ deningerPrimeSections n1 n2 α β V) :
    ∃ f ∈ deningerPrimeSections n1 n2 α β U, deningerPrimeRestrict V f = g := by
  obtain ⟨hg0, hg1, hg2⟩ := hg
  refine ⟨g, ⟨fun p hp => hg0 p fun hcon => hp (deningerPrimeIndex_mono hVU hcon), hg1, hg2⟩, ?_⟩
  funext p
  by_cases hp : p ∈ deningerPrimeIndex V
  · exact deningerPrimeRestrict_of_mem hp
  · rw [deningerPrimeRestrict_of_notMem hp, hg0 p hp]

end PrimeSections

section Gluing

variable {E : Nat.Primes → Type*} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
variable {n1 n2 : ∀ p, Seminorm ℝ (E p)} {α β : Nat.Primes → NNReal}

/-- Every open of the arithmetic base is quasi-compact, because it is a Noetherian space. -/
theorem deningerArithmeticOpen_isCompact (U : Opens (PrimeSpectrum ℤ)) :
    IsCompact (U : Set (PrimeSpectrum ℤ)) :=
  NoetherianSpace.isCompact _

/-- **The sheaf axiom, unique-gluing form.**  A compatible family of sections over a cover of an
arithmetic open glues uniquely.  Quasi-compactness reduces the cover to a finite one, and the glued
family is dominated by the finite sum of the covering families; uniqueness is coordinatewise. -/
theorem deningerPrimeSections_unique_gluing
    {ι : Type} (U : ι → Opens (PrimeSpectrum ℤ)) (f : ι → (∀ p, E p))
    (hf : ∀ i, f i ∈ deningerPrimeSections n1 n2 α β (U i))
    (hcompat : ∀ i j, ∀ p, p ∈ deningerPrimeIndex (U i) → p ∈ deningerPrimeIndex (U j) →
      f i p = f j p) :
    ∃! g : ∀ p, E p, g ∈ deningerPrimeSections n1 n2 α β (iSup U)
      ∧ ∀ i, deningerPrimeRestrict (U i) g = f i := by
  classical
  set g : ∀ p, E p :=
    fun p => if h : ∃ i, p ∈ deningerPrimeIndex (U i) then f h.choose p else 0 with hgdef
  -- the glued family agrees with every covering section where both are defined
  have hgval : ∀ (p : Nat.Primes) (i : ι), p ∈ deningerPrimeIndex (U i) → g p = f i p := by
    intro p i hpi
    have hex : ∃ i, p ∈ deningerPrimeIndex (U i) := ⟨i, hpi⟩
    rw [hgdef]
    simp only [dif_pos hex]
    exact hcompat _ _ p hex.choose_spec hpi
  have hgzero : ∀ p : Nat.Primes, (¬ ∃ i, p ∈ deningerPrimeIndex (U i)) → g p = 0 := by
    intro p hp
    rw [hgdef]
    simp only [dif_neg hp]
  -- a finite subcover
  obtain ⟨s, hs⟩ := (deningerArithmeticOpen_isCompact (iSup U)).elim_finite_subcover
    (fun i => (U i : Set (PrimeSpectrum ℤ))) (fun i => (U i).2) (by
      intro x hx
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hfinite : ∀ p : Nat.Primes, (∃ i, p ∈ deningerPrimeIndex (U i)) →
      ∃ i ∈ s, p ∈ deningerPrimeIndex (U i) := by
    intro p hp
    have hx : deningerPrimeSpectrumPoint p
        ∈ ((iSup U : Opens (PrimeSpectrum ℤ)) : Set (PrimeSpectrum ℤ)) :=
      deningerMem_primeIndex_iSup.mpr hp
    obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact ⟨i, hi, hpi⟩
  -- summability of the glued family, from the finite subcover
  have hmaj1 : Summable fun p => ∑ i ∈ s, (α p : ℝ) * n1 p (f i p) :=
    summable_sum fun i _ => (hf i).2.1
  have hsum1 : Summable fun p => (α p : ℝ) * n1 p (g p) := by
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (α p).coe_nonneg (apply_nonneg _ _))
      (fun p => ?_) hmaj1
    by_cases hp : ∃ i, p ∈ deningerPrimeIndex (U i)
    · obtain ⟨i, his, hpi⟩ := hfinite p hp
      rw [hgval p i hpi]
      exact Finset.single_le_sum (f := fun i => (α p : ℝ) * n1 p (f i p))
        (fun j _ => mul_nonneg (α p).coe_nonneg (apply_nonneg _ _)) his
    · rw [hgzero p hp, map_zero, mul_zero]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (α p).coe_nonneg (apply_nonneg _ _)
  have hmaj2 : Summable fun p => ∑ i ∈ s, (β p : ℝ) * (n2 p (f i p)) ^ 2 :=
    summable_sum fun i _ => (hf i).2.2
  have hsum2 : Summable fun p => (β p : ℝ) * (n2 p (g p)) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (β p).coe_nonneg (by positivity))
      (fun p => ?_) hmaj2
    by_cases hp : ∃ i, p ∈ deningerPrimeIndex (U i)
    · obtain ⟨i, his, hpi⟩ := hfinite p hp
      rw [hgval p i hpi]
      exact Finset.single_le_sum (f := fun i => (β p : ℝ) * (n2 p (f i p)) ^ 2)
        (fun j _ => mul_nonneg (β p).coe_nonneg (by positivity)) his
    · rw [hgzero p hp, map_zero]
      have hz : ((0 : ℝ)) ^ 2 = 0 := by norm_num
      rw [hz, mul_zero]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (β p).coe_nonneg (by positivity)
  have hgmem : g ∈ deningerPrimeSections n1 n2 α β (iSup U) := by
    refine ⟨fun p hp => hgzero p fun hcon => hp (deningerMem_primeIndex_iSup.mpr hcon), hsum1,
      hsum2⟩
  have hgres : ∀ i, deningerPrimeRestrict (U i) g = f i := by
    intro i
    funext p
    by_cases hp : p ∈ deningerPrimeIndex (U i)
    · rw [deningerPrimeRestrict_of_mem hp, hgval p i hp]
    · rw [deningerPrimeRestrict_of_notMem hp, (hf i).1 p hp]
  refine ⟨g, ⟨hgmem, hgres⟩, ?_⟩
  rintro h ⟨hhmem, hhres⟩
  funext p
  by_cases hp : ∃ i, p ∈ deningerPrimeIndex (U i)
  · obtain ⟨i, hpi⟩ := hp
    have h1 : h p = f i p := by
      have := congrFun (hhres i) p
      rwa [deningerPrimeRestrict_of_mem hpi] at this
    rw [h1, hgval p i hpi]
  · rw [hgzero p hp, hhmem.1 p fun hcon => hp (deningerMem_primeIndex_iSup.mp hcon)]

end Gluing

end RHTower
