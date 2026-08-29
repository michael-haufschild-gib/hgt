import GaloisForLFunctions.HTGeometry.RationalPoleOrder
import GaloisForLFunctions.HTGeometry.QDifferenceRatFuncEmbedding
import GaloisForLFunctions.HTGeometry.TwistedDilationOrbitObstruction

/-!
# Principal-part coefficients of a rational function

The coefficient of `(x − c)^(−d)` in the expansion of a rational function at `c` is read off from
the Laurent expansion at the origin of its translate.  It is additive, vanishes wherever the
function is regular, and transforms by the factor `q^(−d)` under the dilation `x ↦ qx`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- Translation of polynomials: `P ↦ P(X + c)`. -/
def polyShift (c : K) : Polynomial K →+* Polynomial K :=
  (Polynomial.aeval (Polynomial.X + Polynomial.C c : Polynomial K)).toRingHom

theorem polyShift_apply (c : K) (P : Polynomial K) :
    polyShift c P = P.comp (Polynomial.X + Polynomial.C c) := by
  rw [polyShift]
  show Polynomial.aeval (Polynomial.X + Polynomial.C c : Polynomial K) P = _
  rw [Polynomial.aeval_def, Polynomial.comp, Polynomial.algebraMap_eq]

theorem polyShift_shift (c : K) (P : Polynomial K) :
    polyShift c (polyShift (-c) P) = P := by
  have hcomp : ((Polynomial.X + Polynomial.C (-c) : Polynomial K).comp
      (Polynomial.X + Polynomial.C c)) = Polynomial.X := by
    rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, map_neg]
    ring
  rw [polyShift_apply, polyShift_apply, Polynomial.comp_assoc, hcomp, Polynomial.comp_X]

theorem polyShift_injective (c : K) : Function.Injective (polyShift (K := K) c) := by
  intro P₁ P₂ h
  have h1 := congrArg (polyShift (-c)) h
  rw [show ∀ Q : Polynomial K, polyShift (-c) (polyShift c Q) = Q from by
    intro Q
    have := polyShift_shift (-c) Q
    rwa [neg_neg] at this] at h1
  rw [show ∀ Q : Polynomial K, polyShift (-c) (polyShift c Q) = Q from by
    intro Q
    have := polyShift_shift (-c) Q
    rwa [neg_neg] at this] at h1
  exact h1

/-- Translation of rational functions: `f ↦ f(X + c)`. -/
def ratFuncShift (c : K) : RatFunc K →+* RatFunc K :=
  RatFunc.mapRingHom (polyShift c)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyShift_injective c))

theorem ratFuncShift_div (c : K) (P S : Polynomial K) :
    ratFuncShift c (algebraMap (Polynomial K) (RatFunc K) P /
        algebraMap (Polynomial K) (RatFunc K) S)
      = algebraMap (Polynomial K) (RatFunc K) (polyShift c P) /
        algebraMap (Polynomial K) (RatFunc K) (polyShift c S) :=
  RatFunc.map_apply_div (polyShift c)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyShift_injective c)) P S

/-- The coefficient of `(x − c)^(−d)` in the expansion of `g` at `c`. -/
def polePart (g : RatFunc K) (c : K) (d : ℕ) : K :=
  (algebraMap (RatFunc K) (LaurentSeries K) (ratFuncShift c g)).coeff (-(d : ℤ))

@[simp]
theorem polePart_add (g₁ g₂ : RatFunc K) (c : K) (d : ℕ) :
    polePart (g₁ + g₂) c d = polePart g₁ c d + polePart g₂ c d := by
  rw [polePart, polePart, polePart, map_add, map_add, HahnSeries.coeff_add]

@[simp]
theorem polePart_zero (c : K) (d : ℕ) : polePart (0 : RatFunc K) c d = 0 := by
  rw [polePart, map_zero, map_zero, HahnSeries.coeff_zero]

@[simp]
theorem polePart_neg (g : RatFunc K) (c : K) (d : ℕ) :
    polePart (-g) c d = -polePart g c d := by
  rw [polePart, polePart, map_neg, map_neg, HahnSeries.coeff_neg]

theorem polePart_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc K) (c : K) (d : ℕ) :
    polePart (∑ i ∈ s, f i) c d = ∑ i ∈ s, polePart (f i) c d := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, polePart_add, ih]

theorem polePart_smul (a : K) (g : RatFunc K) (c : K) (d : ℕ) :
    polePart (algebraMap K (RatFunc K) a * g) c d = a * polePart g c d := by
  rw [polePart, polePart, map_mul, map_mul]
  have hconst : ratFuncShift c (algebraMap K (RatFunc K) a) = algebraMap K (RatFunc K) a := by
    have hC : algebraMap K (RatFunc K) a
        = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) := (RatFunc.algebraMap_C a).symm
    have h := ratFuncShift_div c (Polynomial.C a) 1
    simp only [map_one, div_one] at h
    rw [hC, h, polyShift_apply, Polynomial.C_comp]
  rw [hconst, algebraMap_const_laurentSeries, ← HahnSeries.C_apply, coeff_C_mul_hahn]

/-! ## Vanishing at regular points -/

theorem coeff_neg_algebraMap_eq_zero_of_denom_ne_zero (P Q : Polynomial K) (hQ : Q.eval 0 ≠ 0)
    (n : ℤ) (hn : n < 0) :
    (algebraMap (RatFunc K) (LaurentSeries K)
      (algebraMap (Polynomial K) (RatFunc K) P
        / algebraMap (Polynomial K) (RatFunc K) Q)).coeff n = 0 := by
  have hQ0 : (Q : PowerSeries K) ≠ 0 := by
    intro h
    apply hQ
    have := congrArg PowerSeries.constantCoeff h
    rw [map_zero] at this
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa using this
  have hconst : PowerSeries.constantCoeff (Q : PowerSeries K) ≠ 0 := by
    intro h
    apply hQ
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa using h
  have hinv : ((Q : PowerSeries K)) * ((Q : PowerSeries K))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hconst
  have hcoe : ∀ R : Polynomial K,
      algebraMap (RatFunc K) (LaurentSeries K) (algebraMap (Polynomial K) (RatFunc K) R)
        = ((R : PowerSeries K) : LaurentSeries K) := fun R => (RatFunc.coe_coe R).symm
  have hQne : ((Q : PowerSeries K) : LaurentSeries K) ≠ 0 := by
    intro h
    have := congrArg (fun x : LaurentSeries K => x.coeff 0) h
    rw [PowerSeries.coeff_coe, if_neg (by omega : ¬ (0 : ℤ) < 0), HahnSeries.coeff_zero] at this
    exact hconst (by simpa using this)
  have hdiv : algebraMap (RatFunc K) (LaurentSeries K)
      (algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) Q)
      = (((P : PowerSeries K) * ((Q : PowerSeries K))⁻¹ : PowerSeries K) : LaurentSeries K) := by
    rw [map_div₀, hcoe, hcoe, div_eq_iff hQne, ← map_mul]
    congr 1
    rw [mul_assoc, mul_comm ((Q : PowerSeries K))⁻¹, hinv, mul_one]
  rw [hdiv, PowerSeries.coeff_coe, if_pos hn]

theorem polePart_eq_zero_of_regularAt {g : RatFunc K} {c : K} (h : RegularAt (ratFuncShift c g) 0)
    {d : ℕ} (hd : 0 < d) : polePart g c d = 0 := by
  obtain ⟨P, Q, hQ, hrepr⟩ := h
  rw [polePart, hrepr]
  exact coeff_neg_algebraMap_eq_zero_of_denom_ne_zero P Q hQ _ (by omega)

theorem regularAt_ratFuncShift {g : RatFunc K} {c : K} (h : RegularAt g c) :
    RegularAt (ratFuncShift c g) 0 := by
  obtain ⟨P, Q, hQ, hrepr⟩ := h
  refine ⟨polyShift c P, polyShift c Q, ?_, ?_⟩
  · rw [polyShift_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, zero_add]
    exact hQ
  · rw [hrepr, ratFuncShift_div]

theorem polePart_eq_zero_of_poleOrder_zero {g : RatFunc K} {c : K} {d : ℕ} (hd : 0 < d)
    (h : poleOrder g c = 0) : polePart g c d = 0 :=
  polePart_eq_zero_of_regularAt (regularAt_ratFuncShift ((regularAt_iff_poleOrder_eq_zero g c).mpr h)) hd

theorem finite_support_polePart_multOrbit {g : RatFunc K} {a q : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {d : ℕ} (hd : 0 < d) :
    (Function.support fun n : ℤ => polePart g (multOrbit q a n) d).Finite := by
  classical
  have hroot : {w : K | g.denom.IsRoot w}.Finite :=
    Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero g)
  have hsub : (Function.support fun n : ℤ => polePart g (multOrbit q a n) d) ⊆
      (multOrbit q a) ⁻¹' {w : K | g.denom.IsRoot w} := by
    intro n hn
    rw [Function.mem_support] at hn
    by_contra hcon
    exact hn (polePart_eq_zero_of_poleOrder_zero hd
      (by
        by_contra hz
        exact hcon ((poleOrder_ne_zero_iff g _).mp hz)))
  exact Set.Finite.subset
    (Set.Finite.preimage ((multOrbit_injective hq ha hqtor).injOn) hroot) hsub

/-! ## The dilation law -/

theorem polyShift_polyScale (q c : K) (P : Polynomial K) :
    polyShift c (polyScale q P) = polyScale q (polyShift (q * c) P) := by
  rw [polyShift_apply, polyScale_eq_comp, polyScale_eq_comp, polyShift_apply,
    Polynomial.comp_assoc, Polynomial.comp_assoc]
  congr 1
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, map_mul]
  ring

theorem ratFuncShift_ratFuncScale (q : K) (hq : q ≠ 0) (c : K) (g : RatFunc K) :
    ratFuncShift c (ratFuncScale q hq g) = ratFuncScale q hq (ratFuncShift (q * c) g) := by
  refine RatFunc.induction_on (P := fun g =>
    ratFuncShift c (ratFuncScale q hq g) = ratFuncScale q hq (ratFuncShift (q * c) g)) g ?_
  intro P S _
  rw [ratFuncScale_div, ratFuncShift_div, ratFuncShift_div, ratFuncScale_div,
    polyShift_polyScale, polyShift_polyScale]

theorem polePart_ratFuncScale (q : K) (hq : q ≠ 0) (g : RatFunc K) (c : K) (d : ℕ) :
    polePart (ratFuncScale q hq g) c d = q ^ (-(d : ℤ)) * polePart g (q * c) d := by
  rw [polePart, ratFuncShift_ratFuncScale, algebraMap_ratFuncScale, coeff_innerDilation, polePart]

/-! ## The orbit-mass obstruction -/

theorem telescoping_sum_zero {A B : ℤ → K} {lam : K} (hlam0 : lam ≠ 0)
    (hrel : ∀ n : ℤ, B n = lam * A (n + 1) - A n) (n₀ : ℤ) (M : ℕ) :
    ∑ j ∈ Finset.range M, lam ^ (n₀ + j) * B (n₀ + j)
      = lam ^ (n₀ + M) * A (n₀ + M) - lam ^ n₀ * A n₀ := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hidx : (n₀ + ((M + 1 : ℕ) : ℤ)) = (n₀ + (M : ℤ)) + 1 := by push_cast; ring
      have hexp1 : lam ^ (n₀ + ((M + 1 : ℕ) : ℤ)) = lam ^ (n₀ + (M : ℤ)) * lam := by
        rw [hidx, zpow_add₀ hlam0, zpow_one]
      rw [Finset.sum_range_succ, ih, hrel, hexp1, hidx]
      ring

set_option maxHeartbeats 1000000 in
/-- **The orbit-mass obstruction.**  Along a multiplicative orbit, the top-order principal parts of
a dilation coboundary satisfy a telescoping recursion, so the weighted sum of the principal parts
of the coboundary vanishes.  If the inhomogeneity's top-order principal parts sit at two adjacent
orbit points with a nonzero weighted sum, it is not a coboundary. -/
theorem no_dilationTelescoper_of_orbit_mass {q a : K} (hq : q ≠ 0) (ha : a ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {d : ℕ} (hd : 0 < d) (C : RatFunc K)
    (hsupp : ∀ n : ℤ, n ≠ 0 → n ≠ -1 → polePart C (multOrbit q a n) d = 0)
    (hmass : polePart C a d + q ^ (d : ℤ) * polePart C (multOrbit q a (-1)) d ≠ 0) :
    ¬ ∃ k : RatFunc K, C = ratFuncScale q hq k - k := by
  classical
  rintro ⟨k, rfl⟩
  have hlam0 : (q ^ (-(d : ℤ))) ≠ 0 := zpow_ne_zero _ hq
  have hrel : ∀ n : ℤ,
      polePart (ratFuncScale q hq k - k) (multOrbit q a n) d
        = q ^ (-(d : ℤ)) * polePart k (multOrbit q a (n + 1)) d
          - polePart k (multOrbit q a n) d := by
    intro n
    rw [sub_eq_add_neg, polePart_add, polePart_neg, polePart_ratFuncScale,
      multOrbit_succ q a hq n, sub_eq_add_neg]
  have hfin := finite_support_polePart_multOrbit (g := k) hq ha hqtor hd
  set S : Finset ℤ := hfin.toFinset with hS
  set N : ℕ := S.sup (fun n => n.natAbs) with hN
  have hzero : ∀ n : ℤ, (N : ℤ) < |n| → polePart k (multOrbit q a n) d = 0 := by
    intro n hn
    by_contra hcon
    have hmem : n ∈ S := by
      rw [hS, Set.Finite.mem_toFinset]
      exact hcon
    have hle : n.natAbs ≤ N := Finset.le_sup (f := fun n : ℤ => n.natAbs) hmem
    have habs : |n| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hle
    omega
  have hA1 : polePart k (multOrbit q a (-(N : ℤ) - 1)) d = 0 := by
    refine hzero _ ?_
    rw [abs_of_nonpos (by omega)]
    omega
  have hA2 : polePart k (multOrbit q a (-(N : ℤ) - 1 + ((2 * N + 3 : ℕ) : ℤ))) d = 0 := by
    refine hzero _ ?_
    push_cast
    rw [abs_of_nonneg (by omega)]
    omega
  have hsum0 : ∑ j ∈ Finset.range (2 * N + 3),
      (q ^ (-(d : ℤ))) ^ (-(N : ℤ) - 1 + (j : ℤ))
        * polePart (ratFuncScale q hq k - k) (multOrbit q a (-(N : ℤ) - 1 + (j : ℤ))) d = 0 := by
    rw [telescoping_sum_zero (A := fun n => polePart k (multOrbit q a n) d)
      (B := fun n => polePart (ratFuncScale q hq k - k) (multOrbit q a n) d) hlam0 hrel
      (-(N : ℤ) - 1) (2 * N + 3)]
    show (q ^ (-(d : ℤ))) ^ (-(N : ℤ) - 1 + ((2 * N + 3 : ℕ) : ℤ))
        * polePart k (multOrbit q a (-(N : ℤ) - 1 + ((2 * N + 3 : ℕ) : ℤ))) d
      - (q ^ (-(d : ℤ))) ^ (-(N : ℤ) - 1) * polePart k (multOrbit q a (-(N : ℤ) - 1)) d = 0
    rw [hA1, hA2, mul_zero, mul_zero, sub_zero]
  have hpair : ∑ j ∈ Finset.range (2 * N + 3),
      (q ^ (-(d : ℤ))) ^ (-(N : ℤ) - 1 + (j : ℤ))
        * polePart (ratFuncScale q hq k - k) (multOrbit q a (-(N : ℤ) - 1 + (j : ℤ))) d
      = (q ^ (-(d : ℤ))) ^ (-1 : ℤ)
          * polePart (ratFuncScale q hq k - k) (multOrbit q a (-1)) d
        + (q ^ (-(d : ℤ))) ^ (0 : ℤ)
          * polePart (ratFuncScale q hq k - k) (multOrbit q a 0) d := by
    rw [← Finset.sum_subset (s₁ := ({N, N + 1} : Finset ℕ))
      (s₂ := Finset.range (2 * N + 3))]
    · rw [Finset.sum_pair (by omega : N ≠ N + 1)]
      congr 2 <;> push_cast <;> ring_nf
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_range]
      omega
    · intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      push_neg at hx
      have h1 : (-(N : ℤ) - 1 + (x : ℤ)) ≠ 0 := by
        intro hcon
        exact hx.2 (by omega)
      have h2 : (-(N : ℤ) - 1 + (x : ℤ)) ≠ -1 := by
        intro hcon
        exact hx.1 (by omega)
      rw [hsupp _ h1 h2, mul_zero]
  rw [hpair, multOrbit_zero, zpow_zero, one_mul] at hsum0
  refine hmass ?_
  have hlaminv : (q ^ (-(d : ℤ))) ^ (-1 : ℤ) = q ^ (d : ℤ) := by
    rw [← zpow_mul]
    ring_nf
  rw [hlaminv] at hsum0
  linear_combination hsum0

end

end GaloisForLFunctions.HTGeometry
