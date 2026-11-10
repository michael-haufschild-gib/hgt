import GaloisForLFunctions.HyperbolicArakelovTheory.TheRadialCoordinateOnAdelicVertices
import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePlacesAreTrees

/-!
# The local Green kernel on actual adelic vertices

Integral diagonal reduction and the explicit prime neighbours determine
the radial recurrence on lattice-homothety classes. Its source coefficient
fixes the local Green normalization, including the tempered edge.
-/

set_option autoImplicit false
noncomputable section
open Matrix Set
open scoped Classical BigOperators

namespace GaloisForLFunctions.HyperbolicArakelovTheory.AdelicGreen
open FullAdelic AdelicAdjacency AdelicRadial

local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩
variable (p : {p : ℕ // p.Prime})

private theorem prime_pos : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
private theorem prime_one_lt : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
private theorem prime_ne_zero : (p.1 : ℚ_[p.1]) ≠ 0 := by exact_mod_cast p.2.ne_zero

private theorem norm_prime_le_one : ‖(p.1 : ℚ_[p.1])‖ ≤ 1 := (p.1 : ℤ_[p.1]).2

private theorem norm_nonunit_le_prime (d : ℤ_[p.1]) (hd : ‖(d : ℚ_[p.1])‖ < 1) :
    ‖(d : ℚ_[p.1])‖ ≤ ‖(p.1 : ℚ_[p.1])‖ := by
  obtain ⟨e, he⟩ := (PadicInt.norm_lt_one_iff_dvd d).mp hd
  have hec := congrArg (fun x : ℤ_[p.1] => (x : ℚ_[p.1])) he
  rw [PadicInt.coe_mul, PadicInt.coe_natCast] at hec
  rw [hec, norm_mul]
  exact (mul_le_mul_of_nonneg_left e.2 (norm_nonneg _)).trans_eq (mul_one _)

private theorem norm_residue_lift (b : ZMod p.1) (hb : b ≠ 0) :
    ‖(b.val : ℚ_[p.1])‖ = 1 := by
  apply le_antisymm (b.val : ℤ_[p.1]).2
  by_contra h
  have hd := Padic.norm_natCast_lt_one_iff.mp (lt_of_not_ge h)
  have hz := (ZMod.natCast_eq_zero_iff b.val p.1).mpr hd
  rw [ZMod.natCast_zmod_val] at hz
  exact hb hz

private theorem diagonal_mul_some_val (d : ℤ_[p.1]) (hd : (d : ℚ_[p.1]) ≠ 0)
    (b : ZMod p.1) :
    (diagonalGL p d hd * neighborRep p (some b)).val =
      !![(p.1 : ℚ_[p.1]), -(b.val : ℚ_[p.1]); 0, (d : ℚ_[p.1])] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalGL, neighborRep, Matrix.mul_apply, Fin.sum_univ_two]

private theorem ratio_diagonal_step (d : ℤ_[p.1]) (hd : (d : ℚ_[p.1]) ≠ 0) :
    matrixRatio p (diagonalGL p d hd * neighborRep p none) =
      ‖(d : ℚ_[p.1])‖ / (p.1 : ℝ) := by
  have hsmall : ‖(d : ℚ_[p.1]) * (p.1 : ℚ_[p.1])‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ d.2 (norm_nonneg _) (norm_prime_le_one p)
  have he : diagonalGL p d hd * neighborRep p none =
      diagonalGL p ((d : ℚ_[p.1]) * p.1) (mul_ne_zero hd (prime_ne_zero p)) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalGL, neighborRep, Matrix.mul_apply, Fin.sum_univ_two]
  rw [he, matrixRatio_diagonal p _ _ hsmall, norm_mul, Padic.norm_p, div_eq_mul_inv]

private theorem ratio_diagonal_some_unit (d : ℤ_[p.1]) (hd : (d : ℚ_[p.1]) ≠ 0)
    (hu : ‖(d : ℚ_[p.1])‖ = 1) (b : ZMod p.1) :
    matrixRatio p (diagonalGL p d hd * neighborRep p (some b)) = (p.1 : ℝ)⁻¹ := by
  have hs : entrySize p (diagonalGL p d hd * neighborRep p (some b)).val = 1 := by
    rw [diagonal_mul_some_val]
    change max (max ‖(p.1 : ℚ_[p.1])‖ ‖-(b.val : ℚ_[p.1])‖)
      (max ‖(0 : ℚ_[p.1])‖ ‖(d : ℚ_[p.1])‖) = 1
    rw [norm_neg, norm_zero, hu, max_eq_right zero_le_one]
    exact max_eq_right (max_le (norm_prime_le_one p) (b.val : ℤ_[p.1]).2)
  unfold matrixRatio
  rw [hs, diagonal_mul_some_val]
  simp [Matrix.det_fin_two, norm_mul, hu, Padic.norm_p]

private theorem ratio_diagonal_some_nonzero (d : ℤ_[p.1]) (hd : (d : ℚ_[p.1]) ≠ 0)
    (b : ZMod p.1) (hb : b ≠ 0) :
    matrixRatio p (diagonalGL p d hd * neighborRep p (some b)) =
      ‖(d : ℚ_[p.1])‖ / (p.1 : ℝ) := by
  have hs : entrySize p (diagonalGL p d hd * neighborRep p (some b)).val = 1 := by
    rw [diagonal_mul_some_val]
    change max (max ‖(p.1 : ℚ_[p.1])‖ ‖-(b.val : ℚ_[p.1])‖)
      (max ‖(0 : ℚ_[p.1])‖ ‖(d : ℚ_[p.1])‖) = 1
    rw [norm_neg, norm_zero, norm_residue_lift p b hb,
      max_eq_right (norm_prime_le_one p), max_eq_right (norm_nonneg _), max_eq_left d.2]
  unfold matrixRatio
  rw [hs, diagonal_mul_some_val]
  simp [Matrix.det_fin_two, norm_mul, Padic.norm_p, div_eq_mul_inv, mul_comm]

private theorem ratio_diagonal_some_zero (d : ℤ_[p.1]) (hd : (d : ℚ_[p.1]) ≠ 0)
    (hlt : ‖(d : ℚ_[p.1])‖ < 1) :
    matrixRatio p (diagonalGL p d hd * neighborRep p (some 0)) =
      (p.1 : ℝ) * ‖(d : ℚ_[p.1])‖ := by
  have hs : entrySize p (diagonalGL p d hd * neighborRep p (some 0)).val =
      ‖(p.1 : ℚ_[p.1])‖ := by
    rw [diagonal_mul_some_val]
    change max (max ‖(p.1 : ℚ_[p.1])‖ ‖-((0 : ZMod p.1).val : ℚ_[p.1])‖)
      (max ‖(0 : ℚ_[p.1])‖ ‖(d : ℚ_[p.1])‖) = ‖(p.1 : ℚ_[p.1])‖
    simp only [ZMod.val_zero, Nat.cast_zero, neg_zero, norm_zero]
    rw [max_eq_left (norm_nonneg _), max_eq_right (norm_nonneg _),
      max_eq_left (norm_nonunit_le_prime p d hlt)]
  have hp0 : (p.1 : ℝ) ≠ 0 := (prime_pos p).ne'
  unfold matrixRatio
  rw [hs, diagonal_mul_some_val]
  rw [Matrix.det_fin_two]
  change ‖(p.1 : ℚ_[p.1]) * (d : ℚ_[p.1]) - -((0 : ZMod p.1).val : ℚ_[p.1]) * 0‖ /
    ‖(p.1 : ℚ_[p.1])‖ ^ 2 = _
  simp only [ZMod.val_zero, Nat.cast_zero, neg_zero,
    zero_mul, sub_zero, norm_mul, Padic.norm_p]
  field_simp

/-- The radial power sum over actual neighbours. -/
def radialSum (s : ℝ) (v : LocalVertex p) : ℝ :=
  ∑ w ∈ neighbors p v, vertexRatio p w ^ s

private theorem neighbors_base :
    neighbors p (baseVertex p) = Finset.univ.image (neighbor p) := by
  ext v
  simp only [mem_neighbors, adjacent_base_iff, Finset.mem_image,
    Finset.mem_univ, true_and, Set.mem_range]

private theorem sum_neighbors_base (f : LocalVertex p → ℝ) :
    (∑ w ∈ neighbors p (baseVertex p), f w) = ∑ i : Option (ZMod p.1), f (neighbor p i) := by
  rw [neighbors_base, Finset.sum_image (neighbor_injective p).injOn]

theorem radialSum_integral_smul (s : ℝ) (k : GL (Fin 2) ℤ_[p.1]) (v : LocalVertex p) :
    radialSum p s (ProjGenLinGroup.mk (integralMap p k) • v) = radialSum p s v := by
  unfold radialSum
  rw [neighbors_smul, Finset.sum_image
    (MulAction.injective (ProjGenLinGroup.mk (integralMap p k))).injOn]
  apply Finset.sum_congr rfl
  intro w hw
  rw [vertexRatio_integral_smul]

private theorem radialSum_diagonal_eq (s : ℝ) (d : ℤ_[p.1]) (hd : (d : ℚ_[p.1]) ≠ 0) :
    radialSum p s (QuotientGroup.mk (ProjGenLinGroup.mk (diagonalGL p d hd))) =
      ∑ i : Option (ZMod p.1), matrixRatio p (diagonalGL p d hd * neighborRep p i) ^ s := by
  have hx : (QuotientGroup.mk (ProjGenLinGroup.mk (diagonalGL p d hd)) : LocalVertex p) =
      ProjGenLinGroup.mk (diagonalGL p d hd) • baseVertex p := by
    change QuotientGroup.mk _ = QuotientGroup.mk (_ * 1)
    rw [mul_one]
  unfold radialSum
  rw [hx, neighbors_smul, Finset.sum_image
    (MulAction.injective (ProjGenLinGroup.mk (diagonalGL p d hd))).injOn, sum_neighbors_base]
  apply Finset.sum_congr rfl
  intro i hi
  change projectiveRatio p (ProjGenLinGroup.mk (diagonalGL p d hd) *
    ProjGenLinGroup.mk (neighborRep p i)) ^ s = _
  rw [← map_mul, projectiveRatio_mk]

private theorem radialSum_diagonal_unit (s : ℝ) (d : ℤ_[p.1]) (hd : (d : ℚ_[p.1]) ≠ 0)
    (hu : ‖(d : ℚ_[p.1])‖ = 1) :
    radialSum p s (QuotientGroup.mk (ProjGenLinGroup.mk (diagonalGL p d hd))) =
      ((p.1 : ℝ) + 1) * ((p.1 : ℝ)⁻¹) ^ s := by
  rw [radialSum_diagonal_eq]
  have hval (i : Option (ZMod p.1)) :
      matrixRatio p (diagonalGL p d hd * neighborRep p i) = (p.1 : ℝ)⁻¹ := by
    cases i with
    | none => rw [ratio_diagonal_step, hu, one_div]
    | some b => exact ratio_diagonal_some_unit p d hd hu b
  simp_rw [hval]
  simp

private theorem radialSum_diagonal_nonunit (s : ℝ) (d : ℤ_[p.1])
    (hd : (d : ℚ_[p.1]) ≠ 0) (hlt : ‖(d : ℚ_[p.1])‖ < 1) :
    radialSum p s (QuotientGroup.mk (ProjGenLinGroup.mk (diagonalGL p d hd))) =
      ((p.1 : ℝ) * ‖(d : ℚ_[p.1])‖) ^ s +
        (p.1 : ℝ) * (‖(d : ℚ_[p.1])‖ / (p.1 : ℝ)) ^ s := by
  rw [radialSum_diagonal_eq, Fintype.sum_option, ratio_diagonal_step]
  have hterm (b : ZMod p.1) :
      matrixRatio p (diagonalGL p d hd * neighborRep p (some b)) ^ s =
        (‖(d : ℚ_[p.1])‖ / (p.1 : ℝ)) ^ s +
          if b = 0 then ((p.1 : ℝ) * ‖(d : ℚ_[p.1])‖) ^ s -
            (‖(d : ℚ_[p.1])‖ / (p.1 : ℝ)) ^ s else 0 := by
    by_cases hb : b = 0
    · subst b
      rw [ratio_diagonal_some_zero p d hd hlt, if_pos rfl]
      ring
    · rw [ratio_diagonal_some_nonzero p d hd b hb, if_neg hb, add_zero]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hcount : (∑ _b : ZMod p.1, (‖(d : ℚ_[p.1])‖ / (p.1 : ℝ)) ^ s) =
      (p.1 : ℝ) * (‖(d : ℚ_[p.1])‖ / (p.1 : ℝ)) ^ s := by simp
  have hsingle : (∑ b : ZMod p.1,
      if b = 0 then ((p.1 : ℝ) * ‖(d : ℚ_[p.1])‖) ^ s -
        (‖(d : ℚ_[p.1])‖ / (p.1 : ℝ)) ^ s else 0) =
      ((p.1 : ℝ) * ‖(d : ℚ_[p.1])‖) ^ s -
        (‖(d : ℚ_[p.1])‖ / (p.1 : ℝ)) ^ s := by simp
  rw [hcount, hsingle]
  ring

private theorem vertex_mk_mul_integral (g : LocalPGL p) (k : GL (Fin 2) ℤ_[p.1]) :
    (QuotientGroup.mk (g * ProjGenLinGroup.mk (integralMap p k)) : LocalVertex p) =
      QuotientGroup.mk g := by
  apply QuotientGroup.eq.mpr
  rw [show (g * ProjGenLinGroup.mk (integralMap p k))⁻¹ * g =
    (ProjGenLinGroup.mk (integralMap p k))⁻¹ by group]
  exact (integralPGL p).inv_mem ⟨k, rfl⟩

/-- The exact radial recurrence on the full projective vertex space. -/
theorem radialSum_eq (s : ℝ) (v : LocalVertex p) :
    radialSum p s v = if vertexRatio p v = 1 then
      ((p.1 : ℝ) + 1) * ((p.1 : ℝ)⁻¹) ^ s else
        ((p.1 : ℝ) ^ s + (p.1 : ℝ) ^ (1 - s)) * vertexRatio p v ^ s := by
  induction v using Quotient.inductionOn with
  | h g =>
    induction g using ProjGenLinGroup.induction_on with
    | mk g =>
      obtain ⟨k, l, d, hd, hg⟩ := exists_integral_diagonal p g
      have hv : (QuotientGroup.mk (ProjGenLinGroup.mk g) : LocalVertex p) =
          ProjGenLinGroup.mk (integralMap p k) •
            QuotientGroup.mk (ProjGenLinGroup.mk (diagonalGL p d hd)) := by
        rw [hg, vertex_mk_mul_integral]
        rfl
      have hval : vertexRatio p (QuotientGroup.mk (ProjGenLinGroup.mk g)) =
          ‖(d : ℚ_[p.1])‖ := by
        rw [hv, vertexRatio_integral_smul, vertexRatio_mk,
          projectiveRatio_mk, matrixRatio_diagonal p d hd d.2]
      have hsum : radialSum p s (QuotientGroup.mk (ProjGenLinGroup.mk g)) =
          radialSum p s (QuotientGroup.mk (ProjGenLinGroup.mk (diagonalGL p d hd))) := by
        rw [hv, radialSum_integral_smul]
      rw [hsum, hval]
      by_cases hu : ‖(d : ℚ_[p.1])‖ = 1
      · rw [if_pos hu, radialSum_diagonal_unit p s d hd hu]
      · rw [if_neg hu, radialSum_diagonal_nonunit p s d hd
          ((lt_or_eq_of_le d.2).resolve_right hu)]
        rw [Real.mul_rpow (prime_pos p).le (norm_nonneg _),
          Real.div_rpow (norm_nonneg _) (prime_pos p).le,
          Real.rpow_sub (prime_pos p) 1 s, Real.rpow_one]
        ring

/-- The same recurrence centred at any actual lattice class. -/
theorem sum_localRatio_pow (s : ℝ) (x y : LocalVertex p) :
    (∑ w ∈ neighbors p y, localRatio p x w ^ s) =
      if localRatio p x y = 1 then ((p.1 : ℝ) + 1) * ((p.1 : ℝ)⁻¹) ^ s else
        ((p.1 : ℝ) ^ s + (p.1 : ℝ) ^ (1 - s)) * localRatio p x y ^ s := by
  induction x using Quotient.inductionOn with
  | h g =>
    have hx : (QuotientGroup.mk g : LocalVertex p) = g • baseVertex p := by
      change QuotientGroup.mk g = QuotientGroup.mk (g * 1)
      rw [mul_one]
    have hR (w : LocalVertex p) : localRatio p (QuotientGroup.mk g) (g • w) = vertexRatio p w := by
      rw [hx, localRatio_smul, localRatio_base]
    have hy : y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
    have hval : localRatio p (QuotientGroup.mk g) y = vertexRatio p (g⁻¹ • y) := by
      rw [hy, hR]
      rw [inv_smul_smul]
    simp only [hval]
    rw [hy, neighbors_smul, Finset.sum_image (MulAction.injective g).injOn]
    simp_rw [hR]
    simp only [inv_smul_smul]
    exact radialSum_eq p s (g⁻¹ • y)

private theorem inverse_power (s : ℝ) : ((p.1 : ℝ)⁻¹) ^ s = ((p.1 : ℝ) ^ s)⁻¹ := by
  simpa only [one_div, Real.one_rpow] using
    Real.div_rpow (x := 1) (y := (p.1 : ℝ)) zero_le_one (prime_pos p).le s

/-- The intrinsic Green kernel of the actual prime correspondence. -/
def localGreen (s : ℝ) (x y : LocalVertex p) : ℝ :=
  treeGreen p.1 s 0 * localRatio p x y ^ s

theorem localGreen_symm (s : ℝ) (x y : LocalVertex p) :
    localGreen p s x y = localGreen p s y x := by
  rw [localGreen, localGreen, localRatio_symm p x y]

theorem localGreen_smul (s : ℝ) (a : LocalPGL p) (x y : LocalVertex p) :
    localGreen p s (a • x) (a • y) = localGreen p s x y := by
  rw [localGreen, localGreen, localRatio_smul]

theorem localGreen_self (s : ℝ) (x : LocalVertex p) :
    localGreen p s x x = treeGreen p.1 s 0 := by
  rw [localGreen, (localRatio_eq_one_iff p x x).mpr rfl, Real.one_rpow, mul_one]

theorem localGreen_pos {s : ℝ} (hs : 0 < s) (x y : LocalVertex p) : 0 < localGreen p s x y := by
  unfold localGreen treeGreen
  simp only [pow_zero, mul_one]
  exact mul_pos
    (div_pos (Real.rpow_pos_of_pos (prime_pos p) s)
      (sub_pos.mpr (Real.one_lt_rpow (prime_one_lt p) (by linarith))))
    (Real.rpow_pos_of_pos (localRatio_pos p x y) s)

/-- The actual neighbour operator has this kernel as a unit point-source fundamental solution. -/
theorem localGreen_resolvent {s : ℝ} (hs : 0 < s) (x y : LocalVertex p) :
    treeEigen p.1 s * localGreen p s x y -
      (∑ w ∈ neighbors p y, localGreen p s x w) = if x = y then 1 else 0 := by
  simp only [localGreen]
  rw [← Finset.mul_sum, sum_localRatio_pow]
  by_cases hR : localRatio p x y = 1
  · have hxy := (localRatio_eq_one_iff p x y).mp hR
    rw [if_pos hR, hR, Real.one_rpow, mul_one, if_pos hxy]
    have hroot := treeGreen_resolvent (prime_one_lt p) hs 0
    have hstep : treeGreen p.1 s 1 = treeGreen p.1 s 0 * ((p.1 : ℝ)⁻¹) ^ s := by
      simp only [treeGreen, pow_zero, pow_one, mul_one]
      rw [Real.rpow_neg (prime_pos p).le, inverse_power]
    simp only [treeAdj, if_true] at hroot
    rw [hstep] at hroot
    linear_combination hroot
  · have hxy : x ≠ y := fun h => hR ((localRatio_eq_one_iff p x y).mpr h)
    rw [if_neg hR, if_neg hxy]
    unfold treeEigen
    ring

/-- The source identity remains exact at the tempered spectral edge. -/
theorem localGreen_tempered_resolvent (x y : LocalVertex p) :
    (2 * Real.sqrt p.1) * localGreen p (1 / 2) x y -
      (∑ w ∈ neighbors p y, localGreen p (1 / 2) x w) = if x = y then 1 else 0 := by
  have hEigen : treeEigen p.1 (1 / 2) = 2 * Real.sqrt p.1 :=
    (treeEigen_eq_iff (prime_one_lt p) (1 / 2)).mpr rfl
  rw [← hEigen]
  exact localGreen_resolvent p (by norm_num) x y

/-- The unit source fixes the critical diagonal, independently of the vertex. -/
theorem localGreen_tempered_self (x : LocalVertex p) :
    localGreen p (1 / 2) x x = Real.sqrt p.1 / ((p.1 : ℝ) - 1) := by
  rw [localGreen_self]
  simp only [treeGreen, pow_zero, mul_one]
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Actual vertices along the standard prime apartment. -/
def apartmentVertex (k : ℕ) : LocalVertex p :=
  QuotientGroup.mk (ProjGenLinGroup.mk
    (diagonalGL p ((p.1 : ℚ_[p.1]) ^ k) (pow_ne_zero k (prime_ne_zero p))))

theorem vertexRatio_apartment (k : ℕ) :
    vertexRatio p (apartmentVertex p k) = ((p.1 : ℝ)⁻¹) ^ k := by
  have hsmall : ‖(p.1 : ℚ_[p.1]) ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_prime_le_one p)
  rw [apartmentVertex, vertexRatio_mk, projectiveRatio_mk,
    matrixRatio_diagonal p _ _ hsmall, norm_pow, Padic.norm_p]

/-- The previously computed tree profile is the restriction of the actual local Green kernel. -/
theorem localGreen_apartment (s : ℝ) (k : ℕ) :
    localGreen p s (baseVertex p) (apartmentVertex p k) = treeGreen p.1 s k := by
  have hp : 0 ≤ (p.1 : ℝ)⁻¹ := inv_nonneg.mpr (prime_pos p).le
  have hpower : (((p.1 : ℝ)⁻¹) ^ k) ^ s = ((p.1 : ℝ) ^ (-s)) ^ k := by
    calc
      (((p.1 : ℝ)⁻¹) ^ k) ^ s = ((p.1 : ℝ)⁻¹) ^ ((k : ℝ) * s) := by
        rw [Real.rpow_mul hp, Real.rpow_natCast]
      _ = ((p.1 : ℝ)⁻¹) ^ (s * (k : ℝ)) := by rw [mul_comm (k : ℝ) s]
      _ = (((p.1 : ℝ)⁻¹) ^ s) ^ k := by rw [Real.rpow_mul hp, Real.rpow_natCast]
      _ = ((p.1 : ℝ) ^ (-s)) ^ k := by rw [inverse_power, Real.rpow_neg (prime_pos p).le]
  rw [localGreen, localRatio_base, vertexRatio_apartment, hpower]
  simp only [treeGreen, pow_zero, mul_one]

/-- Weil's prime-power contribution is the normalized critical kernel on actual lattice classes. -/
theorem weilPrimeKernel_eq_localGreen {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) :
    ArithmeticEffectivityTheory.weilPrimeKernel m (m * p.1 ^ k) =
      Real.log p.1 * (((p.1 : ℝ) - 1) / Real.sqrt p.1) *
        localGreen p (1 / 2) (baseVertex p) (apartmentVertex p k) := by
  rw [localGreen_apartment]
  exact weilPrimeKernel_mul_pow_eq_treeGreen p.2 hm hk

#print axioms radialSum_eq
#print axioms localGreen_resolvent
#print axioms localGreen_tempered_resolvent
#print axioms localGreen_symm
#print axioms localGreen_smul
#print axioms localGreen_apartment
#print axioms weilPrimeKernel_eq_localGreen

end GaloisForLFunctions.HyperbolicArakelovTheory.AdelicGreen
