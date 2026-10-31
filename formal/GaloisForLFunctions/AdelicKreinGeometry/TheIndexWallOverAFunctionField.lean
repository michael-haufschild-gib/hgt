import GaloisForLFunctions.AdelicKreinGeometry.TheIndexWallIsLocal
import GaloisForLFunctions.AdelicKreinGeometry.TheAffineGroupOfAField
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# The index wall over a function field

Calibration of the local index wall (`TheIndexWallIsLocal`) over `𝔽_q(X)`, at the place `∞` of
degree one, with residue field `𝔽_q`. For `x ↦ ax + b` over `F(X)`, `F` finite with `q` elements, the
**local Hecke state at `∞`** (`inftyHecke`) is

  `φ_{∞,s}(x ↦ ax + b) = q^{−s|deg a|} · 1[deg b ≤ max(0, deg a)]`,

the condition saying that the image `aO_∞ + b` of the valuation ring `O_∞ = {deg ≤ 0}` meets `O_∞`.

* **Local positivity** (`isPosDefKernel_inftyHecke`): for `s ≥ 1/2` the state is positive definite.
  After clearing denominators, `g_i⁻¹g_j` has slope `A_j/A_i` and shift `(C_j − C_i)/A_i`, and the
  local Haar state is the overlap kernel of the cosets `C_i + F[X]_{≤ deg A_i}`
  (`inftyHecke_half_of_poly`); on coefficient vectors of length `N + 1` the coset is the cylinder of
  vectors agreeing with `C_i` above `deg A_i`, of size `q^{deg A_i + 1}`, so the kernel is a Gram
  matrix (`inftyCommKernel_gram`). The exponent splits off a Poisson kernel `r^{|deg a|}`.
* **Escape** (`inftyHecke_escape`): translation by `X^M`, `M` large, moves every ball off `O_∞`.
* **Negativity** (`one_le_negIndex_inftyHecke`): for `s < 1/2` the dilation by `X` against the `q`
  translations by `cX`, `c ∈ F`, gives the form `q − q²·q^{−2s} < 0`.
* **The wall** (`negIndex_inftyHecke`): `κ(φ_{∞,s}) = 0` for `s ≥ 1/2` and `∞` for `s < 1/2`.

So the wall at `s = 1/2` is not a feature of `ℚ`: over `𝔽_q(X)` the same jump happens at a place
of degree one, with the residue cardinality `q` in the role of `p`.
-/

open Complex Finset Polynomial
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticKreinLangerTheory (isPosDefKernel_poissonKernel)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### The overlap kernel of polynomial cosets -/

/-- The overlap kernel of the cosets `C + F[X]_{≤ d}` and `C' + F[X]_{≤ d'}`: `q^{−|d − d'|/2}` if they
meet, else `0`. -/
def inftyCommKernel (d : ℕ) (C : F[X]) (d' : ℕ) (C' : F[X]) : ℝ :=
  if C' - C = 0 ∨ (C' - C).natDegree ≤ max d d' then
    (Fintype.card F : ℝ) ^ (-(|(d : ℝ) - d'| / 2)) else 0

/-- Agreement of a coefficient vector with `C` above degree `d`. -/
def AgreesAbove {N : ℕ} (d : ℕ) (C : F[X]) (v : Fin (N + 1) → F) : Prop :=
  ∀ j : Fin (N + 1), d < (j : ℕ) → v j = C.coeff j

instance {N : ℕ} (d : ℕ) (C : F[X]) : DecidablePred (AgreesAbove (N := N) d C) := fun v => by
  unfold AgreesAbove; infer_instance

/-- The coset `C + F[X]_{≤ d}` as a weighted indicator on coefficient vectors. -/
def cosetVec {N : ℕ} (d : ℕ) (C : F[X]) (v : Fin (N + 1) → F) : ℝ :=
  if AgreesAbove d C v then (Fintype.card F : ℝ) ^ (-((d : ℝ) + 1) / 2) else 0

/-- A cylinder fixing the coefficients above `d ≤ N` has `q^{d + 1}` elements. -/
theorem card_agreesAbove {N d : ℕ} (hd : d ≤ N) (C : F[X]) :
    Fintype.card {v : Fin (N + 1) → F // AgreesAbove d C v} = Fintype.card F ^ (d + 1) := by
  classical
  let e : {v : Fin (N + 1) → F // AgreesAbove d C v} ≃ (Fin (d + 1) → F) :=
    { toFun := fun v k => v.1 ⟨k, by omega⟩
      invFun := fun w => ⟨fun j => if h : (j : ℕ) ≤ d then w ⟨j, by omega⟩ else C.coeff j,
        fun j hj => by simp [show ¬ (j : ℕ) ≤ d by omega]⟩
      left_inv := fun v => by
        ext j
        by_cases h : (j : ℕ) ≤ d
        · simp [h]
        · simp only [h, dite_false]
          exact (v.2 j (by omega)).symm
      right_inv := fun w => by
        funext k
        simp [show (k : ℕ) ≤ d by omega] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]

omit [Fintype F] in
/-- The coefficient form of the meeting condition. -/
theorem meet_iff {N d d' : ℕ} {C C' : F[X]} (hC : C.natDegree ≤ N) (hC' : C'.natDegree ≤ N) :
    (C' - C = 0 ∨ (C' - C).natDegree ≤ max d d') ↔
      ∀ j : Fin (N + 1), max d d' < (j : ℕ) → C.coeff j = C'.coeff j := by
  constructor
  · rintro (h | h) j hj
    · rw [sub_eq_zero.mp h]
    · have := Polynomial.coeff_eq_zero_of_natDegree_lt (p := C' - C) (n := j) (by omega)
      rw [Polynomial.coeff_sub, sub_eq_zero] at this
      exact this.symm
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨h0, hdeg⟩ := hne
    have hle : (C' - C).natDegree ≤ N :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le hC' hC)
    have := h ⟨(C' - C).natDegree, by omega⟩ hdeg
    have hlead : (C' - C).coeff (C' - C).natDegree = 0 := by
      rw [Polynomial.coeff_sub, ← this, sub_self]
    exact h0 (Polynomial.leadingCoeff_eq_zero.mp hlead)

/-- The model inner product of two cosets is their overlap kernel. -/
theorem sum_cosetVec_mul_of_le {N d d' : ℕ} {C C' : F[X]} (hdd : d ≤ d') (hd' : d' ≤ N)
    (hC : C.natDegree ≤ N) (hC' : C'.natDegree ≤ N) :
    ∑ v : Fin (N + 1) → F, cosetVec d C v * cosetVec d' C' v = inftyCommKernel d C d' C' := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpt : ∀ v : Fin (N + 1) → F, cosetVec d C v * cosetVec d' C' v =
      if AgreesAbove d C v ∧ AgreesAbove d' C' v then
        (Fintype.card F : ℝ) ^ (-((d : ℝ) + 1) / 2) * (Fintype.card F : ℝ) ^ (-((d' : ℝ) + 1) / 2)
      else 0 := fun v => by
    unfold cosetVec; split_ifs <;> simp_all
  rw [sum_congr rfl fun v _ => hpt v, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  unfold inftyCommKernel
  by_cases hmeet : C' - C = 0 ∨ (C' - C).natDegree ≤ max d d'
  · rw [if_pos hmeet]
    have hagree := (meet_iff (d := d) (d' := d') hC hC').mp hmeet
    -- agreement with `C` above `d` already gives agreement with `C'` above `d'`
    have hset : (univ.filter fun v : Fin (N + 1) → F => AgreesAbove d C v ∧ AgreesAbove d' C' v) =
        univ.filter fun v => AgreesAbove d C v := by
      ext v
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨fun h => h.1, fun h => ⟨h, fun j hj => ?_⟩⟩
      rw [h j (by omega)]
      exact hagree j (by omega)
    rw [hset, ← Fintype.card_subtype, card_agreesAbove (hdd.trans hd') C]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_add hq, ← Real.rpow_add hq]
    congr 1
    rw [abs_of_nonpos (by have : (d : ℝ) ≤ d' := by exact_mod_cast hdd
                          linarith)]
    push_cast
    ring
  · rw [if_neg hmeet]
    have hempty : (univ.filter fun v : Fin (N + 1) → F =>
        AgreesAbove d C v ∧ AgreesAbove d' C' v) = ∅ := by
      ext v
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro h1 h2
      refine hmeet ((meet_iff hC hC').mpr fun j hj => ?_)
      rw [← h1 j (by omega), h2 j (by omega)]
    rw [hempty, Finset.card_empty]
    simp

theorem inftyCommKernel_comm (d : ℕ) (C : F[X]) (d' : ℕ) (C' : F[X]) :
    inftyCommKernel d C d' C' = inftyCommKernel d' C' d C := by
  have h1 : (C - C' = 0 ∨ (C - C').natDegree ≤ max d' d) ↔
      (C' - C = 0 ∨ (C' - C).natDegree ≤ max d d') := by
    rw [show C - C' = -(C' - C) by ring, neg_eq_zero, Polynomial.natDegree_neg, max_comm]
  unfold inftyCommKernel
  by_cases h : C' - C = 0 ∨ (C' - C).natDegree ≤ max d d'
  · rw [if_pos h, if_pos (h1.mpr h), abs_sub_comm]
  · rw [if_neg h, if_neg (mt h1.mp h)]

theorem sum_cosetVec_mul {N d d' : ℕ} {C C' : F[X]} (hd : d ≤ N) (hd' : d' ≤ N)
    (hC : C.natDegree ≤ N) (hC' : C'.natDegree ≤ N) :
    ∑ v : Fin (N + 1) → F, cosetVec d C v * cosetVec d' C' v = inftyCommKernel d C d' C' := by
  rcases le_total d d' with h | h
  · exact sum_cosetVec_mul_of_le h hd' hC hC'
  · rw [inftyCommKernel_comm, ← sum_cosetVec_mul_of_le h hd hC' hC]
    exact sum_congr rfl fun v _ => mul_comm _ _

/-- **The overlap kernel is positive definite**: its Gram form is `Σ_v |Σ_j c_j f_j(v)|²` over the
coefficient vectors of a common length. -/
theorem inftyCommKernel_gram {n : ℕ} (d : Fin n → ℕ) (C : Fin n → F[X]) (c : Fin n → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ∑ i, ∑ j, star (c i) * (inftyCommKernel (d i) (C i) (d j) (C j) : ℂ) * c j = r := by
  classical
  set N : ℕ := ∑ i, (d i + (C i).natDegree)
  have hdN : ∀ i, d i ≤ N := fun i =>
    le_trans (Nat.le_add_right _ _) (Finset.single_le_sum (f := fun i => d i + (C i).natDegree)
      (fun _ _ => Nat.zero_le _) (mem_univ i))
  have hCN : ∀ i, (C i).natDegree ≤ N := fun i =>
    le_trans (Nat.le_add_left _ _) (Finset.single_le_sum (f := fun i => d i + (C i).natDegree)
      (fun _ _ => Nat.zero_le _) (mem_univ i))
  set S : (Fin (N + 1) → F) → ℂ := fun v => ∑ j, c j * (cosetVec (d j) (C j) v : ℂ)
  refine ⟨∑ v : Fin (N + 1) → F, Complex.normSq (S v),
    sum_nonneg fun v _ => Complex.normSq_nonneg _, ?_⟩
  have hK : ∀ i j, (inftyCommKernel (d i) (C i) (d j) (C j) : ℂ) =
      ∑ v : Fin (N + 1) → F, ((cosetVec (d i) (C i) v : ℝ) : ℂ) * ((cosetVec (d j) (C j) v : ℝ) : ℂ) :=
    fun i j => by
      rw [← sum_cosetVec_mul (hdN i) (hdN j) (hCN i) (hCN j)]
      push_cast; rfl
  simp_rw [hK]
  have hR : ∀ v, (Complex.normSq (S v) : ℂ) = ∑ i, ∑ j,
      star (c i) * ((cosetVec (d i) (C i) v : ℝ) : ℂ) * (((cosetVec (d j) (C j) v : ℝ) : ℂ) * c j) := by
    intro v
    have hstar : star (S v) = ∑ i, star (c i) * ((cosetVec (d i) (C i) v : ℝ) : ℂ) := by
      simp only [S, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, hstar, Finset.sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  set A : Fin n → (Fin (N + 1) → F) → ℂ := fun i v => ((cosetVec (d i) (C i) v : ℝ) : ℂ)
  calc ∑ i, ∑ j, star (c i) * (∑ v, A i v * A j v) * c j
      = ∑ i, ∑ j, ∑ v, star (c i) * A i v * (A j v * c j) := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact sum_congr rfl fun v _ => by ring
    _ = ∑ i, ∑ v, ∑ j, star (c i) * A i v * (A j v * c j) :=
        sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ v, ∑ i, ∑ j, star (c i) * A i v * (A j v * c j) := Finset.sum_comm
    _ = ((∑ v : Fin (N + 1) → F, Complex.normSq (S v) : ℝ) : ℂ) := by
        push_cast
        exact sum_congr rfl fun v _ => (hR v).symm

/-! ### The local Hecke state at infinity -/

omit [Fintype F] [DecidableEq F] in
/-- The degree of the slope, as a homomorphism to `ℤ`. -/
def slopeDeg : AffineGroupOf (RatFunc F) →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (slopeOf g).intDegree
  map_one' := by simp [slopeOf_one]
  map_mul' g h := by
    rw [slopeOf_mul, RatFunc.intDegree_mul (slopeOf_ne_zero g) (slopeOf_ne_zero h), ofAdd_add]

omit [Fintype F] [DecidableEq F] in
theorem toAdd_slopeDeg (g : AffineGroupOf (RatFunc F)) :
    Multiplicative.toAdd (slopeDeg g) = (slopeOf g).intDegree := rfl

/-- **The local Hecke state at `∞`**: `q^{−s|deg a|}` if `aO_∞ + b` meets `O_∞`, else `0`. -/
def inftyHecke (s : ℝ) (g : AffineGroupOf (RatFunc F)) : ℂ :=
  if (shiftOf g).intDegree ≤ max 0 (slopeOf g).intDegree then
    (((Fintype.card F : ℝ) ^ (-(s * |((slopeOf g).intDegree : ℝ)|)) : ℝ) : ℂ) else 0

omit [DecidableEq F] in
theorem inftyHecke_eq_mul (s : ℝ) (g : AffineGroupOf (RatFunc F)) :
    inftyHecke s g = inftyHecke (1 / 2) g * ArithmeticKreinLangerTheory.poissonKernel
      ((Fintype.card F : ℝ) ^ (-(s - 1 / 2))) (slopeDeg g) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  simp only [inftyHecke, ArithmeticKreinLangerTheory.poissonKernel, toAdd_slopeDeg]
  split_ifs
  · rw [← Complex.ofReal_mul, ← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_add hq,
      Nat.cast_natAbs, Int.cast_abs]
    congr 2
    ring
  · simp

omit [Fintype F] [DecidableEq F] in
theorem intDegree_algebraMap (P : F[X]) :
    (algebraMap F[X] (RatFunc F) P).intDegree = P.natDegree := RatFunc.intDegree_polynomial

/-- **The local Haar state at `∞` in polynomial coordinates.** -/
theorem inftyHecke_half_of_poly {g : AffineGroupOf (RatFunc F)} {A A' C C' : F[X]} (hA : A ≠ 0)
    (hA' : A' ≠ 0)
    (hsl : slopeOf g = algebraMap F[X] (RatFunc F) A' / algebraMap F[X] (RatFunc F) A)
    (hsh : shiftOf g = algebraMap F[X] (RatFunc F) (C' - C) / algebraMap F[X] (RatFunc F) A) :
    inftyHecke (1 / 2) g = (inftyCommKernel A.natDegree C A'.natDegree C' : ℂ) := by
  have hAr : algebraMap F[X] (RatFunc F) A ≠ 0 := RatFunc.algebraMap_ne_zero hA
  have hA'r : algebraMap F[X] (RatFunc F) A' ≠ 0 := RatFunc.algebraMap_ne_zero hA'
  have hvs : (slopeOf g).intDegree = (A'.natDegree : ℤ) - A.natDegree := by
    rw [hsl, div_eq_mul_inv, RatFunc.intDegree_mul hA'r (inv_ne_zero hAr), RatFunc.intDegree_inv,
      intDegree_algebraMap, intDegree_algebraMap]
    ring
  have hcond : (shiftOf g).intDegree ≤ max 0 (slopeOf g).intDegree ↔
      (C' - C = 0 ∨ (C' - C).natDegree ≤ max A.natDegree A'.natDegree) := by
    rw [hvs, hsh]
    by_cases hE : C' - C = 0
    · simp [hE]
    · have hEr : algebraMap F[X] (RatFunc F) (C' - C) ≠ 0 := RatFunc.algebraMap_ne_zero hE
      rw [div_eq_mul_inv, RatFunc.intDegree_mul hEr (inv_ne_zero hAr), RatFunc.intDegree_inv,
        intDegree_algebraMap, intDegree_algebraMap]
      simp only [hE, false_or]
      omega
  unfold inftyHecke inftyCommKernel
  by_cases h : (shiftOf g).intDegree ≤ max 0 (slopeOf g).intDegree
  · rw [if_pos h, if_pos (hcond.mp h), hvs]
    congr 2
    push_cast
    rw [abs_sub_comm]
    ring
  · rw [if_neg h, if_neg (mt hcond.mpr h)]; simp

omit [Fintype F] [DecidableEq F] in
/-- Clearing a denominator. -/
theorem exists_poly_eq_mul (f : RatFunc F) {D : F[X]} (hD : f.denom ∣ D) :
    ∃ P : F[X], algebraMap F[X] (RatFunc F) P = algebraMap F[X] (RatFunc F) D * f := by
  obtain ⟨E, hE⟩ := hD
  refine ⟨E * f.num, ?_⟩
  have hden : algebraMap F[X] (RatFunc F) f.denom ≠ 0 := RatFunc.algebraMap_ne_zero f.denom_ne_zero
  have hf : algebraMap F[X] (RatFunc F) f.denom * f = algebraMap F[X] (RatFunc F) f.num := by
    have h := RatFunc.num_div_denom f
    rw [div_eq_iff hden] at h
    rw [h]; ring
  rw [hE, map_mul, map_mul, mul_comm (algebraMap _ _ f.denom), mul_assoc, hf]

/-- **The local Haar state at `∞` is positive definite.** -/
theorem isPosDefOnGroup_inftyHaar : IsPosDefOnGroup (inftyHecke (F := F) (1 / 2)) := by
  intro n x c
  classical
  set a : Fin n → RatFunc F := fun i => slopeOf (x i)
  set b : Fin n → RatFunc F := fun i => shiftOf (x i)
  set D : F[X] := ∏ i, ((a i).denom * (b i).denom)
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
    mul_ne_zero (a i).denom_ne_zero (b i).denom_ne_zero
  have hDr : algebraMap F[X] (RatFunc F) D ≠ 0 := RatFunc.algebraMap_ne_zero hD
  have hdvd_a : ∀ i, (a i).denom ∣ D := fun i =>
    (dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (mem_univ i))
  have hdvd_b : ∀ i, (b i).denom ∣ D := fun i =>
    (dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (mem_univ i))
  choose A hA using fun i => exists_poly_eq_mul (a i) (hdvd_a i)
  choose C hC using fun i => exists_poly_eq_mul (b i) (hdvd_b i)
  have hA0 : ∀ i, A i ≠ 0 := fun i h => by
    have e := hA i
    rw [h, map_zero] at e
    rcases mul_eq_zero.mp e.symm with h' | h'
    · exact hDr h'
    · exact slopeOf_ne_zero (x i) h'
  have ea : ∀ i, a i = algebraMap F[X] (RatFunc F) (A i) / algebraMap F[X] (RatFunc F) D :=
    fun i => by rw [hA i]; field_simp
  have eb : ∀ i, b i = algebraMap F[X] (RatFunc F) (C i) / algebraMap F[X] (RatFunc F) D :=
    fun i => by rw [hC i]; field_simp
  have key : ∀ i j, inftyHecke (1 / 2) ((x i)⁻¹ * x j) =
      (inftyCommKernel (A i).natDegree (C i) (A j).natDegree (C j) : ℂ) := by
    intro i j
    have hAi : algebraMap F[X] (RatFunc F) (A i) ≠ 0 := RatFunc.algebraMap_ne_zero (hA0 i)
    have hsl : slopeOf ((x i)⁻¹ * x j) =
        algebraMap F[X] (RatFunc F) (A j) / algebraMap F[X] (RatFunc F) (A i) := by
      rw [slopeOf_mul, slopeOf_inv]
      change (a i)⁻¹ * a j = _
      rw [ea i, ea j]
      field_simp
    have hsh : shiftOf ((x i)⁻¹ * x j) =
        algebraMap F[X] (RatFunc F) (C j - C i) / algebraMap F[X] (RatFunc F) (A i) := by
      rw [shiftOf_mul, shiftOf_inv, slopeOf_inv]
      change (a i)⁻¹ * b j + -b i / a i = _
      rw [ea i, eb i, eb j, map_sub]
      field_simp
      ring
    exact inftyHecke_half_of_poly (hA0 i) (hA0 j) hsl hsh
  obtain ⟨r, hr, h⟩ := inftyCommKernel_gram (fun i => (A i).natDegree) C c
  exact ⟨r, hr, by simp only [key]; exact h⟩

omit [DecidableEq F] in
theorem one_lt_card_field : (1 : ℝ) < Fintype.card F := by
  exact_mod_cast Fintype.one_lt_card

/-- **Positivity at `∞`**: for `s ≥ 1/2` the local Hecke state at `∞` is positive definite. -/
theorem isPosDefKernel_inftyHecke {s : ℝ} (hs : 1 / 2 ≤ s) :
    IsPosDefKernel (inftyHecke (F := F) s) := by
  have e : inftyHecke (F := F) s = fun g => inftyHecke (1 / 2) g *
      (ArithmeticKreinLangerTheory.poissonKernel ((Fintype.card F : ℝ) ^ (-(s - 1 / 2))) ∘
        slopeDeg) g :=
    funext (inftyHecke_eq_mul s)
  rw [e]
  exact IsPosDefKernel.mul (isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_inftyHaar)
    ((isPosDefKernel_poissonKernel (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_le_one_of_one_le_of_nonpos one_lt_card_field.le (by linarith))).comp slopeDeg)

theorem isHermKernel_inftyHecke (s : ℝ) : IsHermKernel (inftyHecke (F := F) s) := fun g => by
  have h1 := (isPosDefKernel_iff_isPosDefOnGroup.mpr (isPosDefOnGroup_inftyHaar (F := F))).1 g
  have h2 := isHermKernel_poissonKernel ((Fintype.card F : ℝ) ^ (-(s - 1 / 2))) (slopeDeg g)
  rw [inftyHecke_eq_mul s g⁻¹, inftyHecke_eq_mul s g, h1, map_inv, h2, map_mul]

/-! ### Escape -/

omit [Fintype F] [DecidableEq F] in
theorem intDegree_X_pow (M : ℕ) : ((RatFunc.X : RatFunc F) ^ M).intDegree = M := by
  rw [← RatFunc.algebraMap_X, ← map_pow, intDegree_algebraMap, Polynomial.natDegree_X_pow]

omit [DecidableEq F] in
/-- **Escape at `∞`**: translation by `X^M`, `M` large, moves every ball `g⁻¹(t·h)(O_∞)` off `O_∞`. -/
theorem inftyHecke_escape (s : ℝ) (m n : ℕ) (x : Fin m → AffineGroupOf (RatFunc F))
    (y : Fin n → AffineGroupOf (RatFunc F)) :
    ∃ t : AffineGroupOf (RatFunc F), ∀ a b, inftyHecke s ((x a)⁻¹ * (t * y b)) = 0 := by
  classical
  set va : Fin m → ℤ := fun a => (slopeOf (x a)).intDegree
  set vb : Fin n → ℤ := fun b => (slopeOf (y b)).intDegree
  set vd : Fin m → Fin n → ℤ := fun a b => (shiftOf (y b) - shiftOf (x a)).intDegree
  set M : ℕ := 1 + ∑ a, ∑ b, (2 * (va a).natAbs + (vb b).natAbs + (vd a b).natAbs)
  set β : RatFunc F := RatFunc.X ^ M
  refine ⟨translationOf β, fun a b => ?_⟩
  have hM : ((2 * (va a).natAbs + (vb b).natAbs + (vd a b).natAbs : ℕ) : ℤ) < M := by
    have h1 : 2 * (va a).natAbs + (vb b).natAbs + (vd a b).natAbs ≤
        ∑ b', (2 * (va a).natAbs + (vb b').natAbs + (vd a b').natAbs) :=
      Finset.single_le_sum (f := fun b' => 2 * (va a).natAbs + (vb b').natAbs + (vd a b').natAbs)
        (fun _ _ => Nat.zero_le _) (mem_univ b)
    have h2 : ∑ b', (2 * (va a).natAbs + (vb b').natAbs + (vd a b').natAbs) ≤
        ∑ a', ∑ b', (2 * (va a').natAbs + (vb b').natAbs + (vd a' b').natAbs) :=
      Finset.single_le_sum
        (f := fun a' => ∑ b', (2 * (va a').natAbs + (vb b').natAbs + (vd a' b').natAbs))
        (fun _ _ => Nat.zero_le _) (mem_univ a)
    exact_mod_cast (show _ < M by omega)
  push_cast at hM
  have hα : slopeOf (x a) ≠ 0 := slopeOf_ne_zero _
  have hβ0 : β ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  have hβ : β.intDegree = M := intDegree_X_pow M
  set δ : RatFunc F := shiftOf (y b) - shiftOf (x a)
  -- the shift `δ + β` has degree `M`
  have hδβ : δ + β ≠ 0 ∧ (δ + β).intDegree = M := by
    by_cases hδ : δ = 0
    · rw [hδ, zero_add]; exact ⟨hβ0, hβ⟩
    · have hlt : δ.intDegree < M := by
        have := le_abs_self (vd a b); linarith [abs_nonneg (va a), abs_nonneg (vb b)]
      have hne : δ + β ≠ 0 := fun h => by
        have : δ = -β := by linear_combination h
        rw [this, RatFunc.intDegree_neg, hβ] at hlt; exact lt_irrefl _ hlt
      refine ⟨hne, le_antisymm ?_ ?_⟩
      · exact (RatFunc.intDegree_add_le hβ0 hne).trans (by rw [hβ]; exact max_le hlt.le le_rfl)
      · have h := RatFunc.intDegree_add_le (x := δ + β) (y := -δ) (neg_ne_zero.mpr hδ)
          (by rw [add_neg_cancel_comm]; exact hβ0)
        rw [add_neg_cancel_comm, hβ, RatFunc.intDegree_neg] at h
        rcases le_max_iff.mp h with h' | h'
        · exact h'
        · exact absurd h' (not_le.mpr hlt)
  have hsl : slopeOf ((x a)⁻¹ * (translationOf β * y b)) = (slopeOf (x a))⁻¹ * slopeOf (y b) := by
    rw [slopeOf_mul, slopeOf_inv, slopeOf_mul, slopeOf_translationOf, one_mul]
  have hsh : shiftOf ((x a)⁻¹ * (translationOf β * y b)) = (δ + β) / slopeOf (x a) := by
    rw [shiftOf_mul, shiftOf_inv, slopeOf_inv, shiftOf_mul, slopeOf_translationOf,
      shiftOf_translationOf]
    simp only [δ]
    field_simp
    ring
  have hvsl : (slopeOf ((x a)⁻¹ * (translationOf β * y b))).intDegree = vb b - va a := by
    rw [hsl, RatFunc.intDegree_mul (inv_ne_zero hα) (slopeOf_ne_zero _), RatFunc.intDegree_inv]
    simp only [va, vb]; ring
  have hvsh : (shiftOf ((x a)⁻¹ * (translationOf β * y b))).intDegree = (M : ℤ) - va a := by
    rw [hsh, div_eq_mul_inv, RatFunc.intDegree_mul hδβ.1 (inv_ne_zero hα), RatFunc.intDegree_inv,
      hδβ.2]
    ring
  unfold inftyHecke
  rw [if_neg]
  rw [hvsl, hvsh, not_le]
  have := le_abs_self (va a)
  have := neg_abs_le (va a)
  have := le_abs_self (vb b)
  exact max_lt (by linarith [abs_nonneg (vb b), abs_nonneg (vd a b)])
    (by linarith [abs_nonneg (vb b), abs_nonneg (vd a b)])

/-! ### Negativity below `1/2` -/

/-- **Negativity at `∞`**: below `1/2` the dilation by `X` and the `q` translations by `cX`, with
weights `−q^{1−s}` and `1`, have form `q − q²·q^{−2s} < 0`. -/
theorem one_le_negIndex_inftyHecke {s : ℝ} (hs : s < 1 / 2) :
    1 ≤ negIndex (inftyHecke (F := F) s) := by
  classical
  have hq1 : (1 : ℝ) < Fintype.card F := one_lt_card_field
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  set uX : (RatFunc F)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero
  set x : Option F → AffineGroupOf (RatFunc F) :=
    fun o => o.elim (dilationOf uX) fun e => translationOf (RatFunc.C e * RatFunc.X)
  set y : ℝ := (Fintype.card F : ℝ) ^ (-s)
  set c : Option F → ℂ := fun o => o.elim (-(((Fintype.card F : ℝ) * y : ℝ) : ℂ)) fun _ => 1
  have hXinv : (RatFunc.X⁻¹ : RatFunc F).intDegree = -1 := by
    rw [RatFunc.intDegree_inv, RatFunc.intDegree_X]
  have h00 : inftyHecke s ((x none)⁻¹ * x none) = 1 := by
    simp [inftyHecke, slopeOf_one, shiftOf_one, RatFunc.intDegree_one, RatFunc.intDegree_zero]
  have h0k : ∀ e : F, inftyHecke s ((x none)⁻¹ * x (some e)) = (y : ℂ) := fun e => by
    have hsl : slopeOf ((x none)⁻¹ * x (some e)) = RatFunc.X⁻¹ := by
      simp [x, uX, slopeOf_mul, slopeOf_inv, slopeOf_dilationOf, slopeOf_translationOf]
    have hsh : shiftOf ((x none)⁻¹ * x (some e)) = RatFunc.C e := by
      simp only [x, Option.elim_none, Option.elim_some, shiftOf_mul, shiftOf_inv, slopeOf_inv,
        slopeOf_dilationOf, shiftOf_dilationOf, shiftOf_translationOf, uX, Units.val_mk0,
        neg_zero, zero_div, add_zero]
      rw [mul_comm, mul_assoc, mul_inv_cancel₀ (RatFunc.X_ne_zero (K := F)), mul_one]
    have hC : (RatFunc.C e : RatFunc F).intDegree = 0 := RatFunc.intDegree_C e
    simp only [inftyHecke, hsl, hsh, hC, hXinv, y]
    rw [if_pos (by norm_num)]
    norm_num
  have hk0 : ∀ e : F, inftyHecke s ((x (some e))⁻¹ * x none) = (y : ℂ) := fun e => by
    rw [show (x (some e))⁻¹ * x none = ((x none)⁻¹ * x (some e))⁻¹ by group,
      isHermKernel_inftyHecke s, h0k, Complex.conj_ofReal]
  have hjk : ∀ e e' : F, inftyHecke s ((x (some e))⁻¹ * x (some e')) =
      if e = e' then 1 else 0 := fun e e' => by
    have hsl : slopeOf ((x (some e))⁻¹ * x (some e')) = 1 := by
      simp [x, slopeOf_mul, slopeOf_inv, slopeOf_translationOf]
    have hsh : shiftOf ((x (some e))⁻¹ * x (some e')) = RatFunc.C (e' - e) * RatFunc.X := by
      simp only [x, Option.elim_some, shiftOf_mul, shiftOf_inv, slopeOf_inv, slopeOf_translationOf,
        shiftOf_translationOf, map_sub]
      field_simp
      ring
    by_cases hee : e = e'
    · subst hee
      simp [inftyHecke, slopeOf_one, shiftOf_one, RatFunc.intDegree_one, RatFunc.intDegree_zero]
    · rw [if_neg hee]
      have hC : RatFunc.C (e' - e) ≠ (0 : RatFunc F) :=
        (_root_.map_ne_zero RatFunc.C).mpr (sub_ne_zero.mpr (Ne.symm hee))
      have hdeg : (RatFunc.C (e' - e) * RatFunc.X : RatFunc F).intDegree = 1 := by
        rw [RatFunc.intDegree_mul hC RatFunc.X_ne_zero, RatFunc.intDegree_C, RatFunc.intDegree_X,
          zero_add]
      simp only [inftyHecke, hsl, hsh, hdeg, RatFunc.intDegree_one]
      rw [if_neg (by norm_num)]
  have hneg : hermQuad (gram (inftyHecke s) x) c < 0 := by
    rw [hermQuad_gram]
    have hsum : ∑ a, ∑ b, conj (c a) * inftyHecke s ((x a)⁻¹ * x b) * c b =
        (((Fintype.card F : ℝ) - (Fintype.card F : ℝ) ^ 2 * (y * y) : ℝ) : ℂ) := by
      simp only [Fintype.sum_option, h00, h0k, hk0, hjk, c, Option.elim_none, Option.elim_some,
        map_neg, Complex.conj_ofReal, map_one, mul_one, one_mul, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      push_cast
      ring
    rw [hsum, Complex.ofReal_re]
    have hyy : y * y = (Fintype.card F : ℝ) ^ (-(2 * s)) := by
      rw [← Real.rpow_add hq0]; ring_nf
    have : (1 : ℝ) < Fintype.card F * (Fintype.card F : ℝ) ^ (-(2 * s)) := by
      rw [← Real.rpow_one_add' hq0.le (by linarith)]
      exact Real.one_lt_rpow hq1 (by linarith)
    rw [hyy]; nlinarith
  have h1 := one_le_negIndexOn (V := ⊤) Submodule.mem_top hneg
  exact le_trans (by exact_mod_cast h1.trans (negIndexOn_le_hermNegIndex _ ⊤))
    (hermNegIndex_gram_le_negIndex (inftyHecke s) _)

/-- **The wall over a function field**: `κ(φ_{∞,s}) = 0` for `s ≥ 1/2` and `∞` for `s < 1/2`. -/
theorem negIndex_inftyHecke (s : ℝ) :
    negIndex (inftyHecke (F := F) s) = if 1 / 2 ≤ s then 0 else ⊤ := by
  split_ifs with hs
  · exact (isPosDefKernel_inftyHecke hs).negIndex_eq_zero
  · rcases negIndex_eq_zero_or_top_of_escape (isHermKernel_inftyHecke (F := F) s)
      (inftyHecke_escape (F := F) s) with h | h
    · have := one_le_negIndex_inftyHecke (F := F) (not_le.mp hs)
      rw [h] at this
      exact absurd this (by norm_num)
    · exact h

end GaloisForLFunctions.AdelicKreinGeometry
