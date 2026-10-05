import GaloisForLFunctions.RHTower.ChiRamanujanWeightedThirdShift
/-!
# Full weighted cubic trace for every distinguished-prime placement

The missing negative offsets are finite diagonal corrections to the actual
weighted local trace. Translation covers all three-slot distinguished shifts,
including coincident prime labels, and finite-product summation retains every
valuation pair and both actual Mellin frequencies. Final actual-prime and
finite-prime families require no hypotheses. Rational node grouping and the
growing physical signed estimate remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace


private lemma coefficient_below (z : ℂ) {i : ℤ} (hi : i < -1) :
    complexCoefficient z i=0 := by
  simp [complexCoefficient,show i ≠ -1 by omega,show ¬0 ≤ i by omega]

def weightedValuationDiagonal (z x y : ℂ) (k : ℤ) (v : ℤ × ℤ) : ℂ :=
  if v.1+v.2=k then complexCoefficient z v.1*complexCoefficient z v.2*x^v.1*y^v.2 else 0

private lemma pair_atom_sum (a b : ℤ) :
    HasSum (fun v : ℤ × ℤ => complexAtom a v.1*complexAtom b v.2) (1 : ℂ) := by
  simpa using (complexAtom_hasSum a).mul (complexAtom_hasSum b)
    (summable_mul_of_summable_norm (complexAtom_hasSum a).summable.norm
      (complexAtom_hasSum b).summable.norm)

theorem weightedValuationDiagonal_hasSum (z x y : ℂ) (k : ℤ) :
    HasSum (weightedValuationDiagonal z x y k)
      (∑ i ∈ Finset.Icc (-1) (k+1),
        complexCoefficient z i*complexCoefficient z (k-i)*x^i*y^(k-i)) := by
  let A (i : ℤ) := complexCoefficient z i*complexCoefficient z (k-i)*x^i*y^(k-i)
  have h := hasSum_sum (s := Finset.Icc (-1) (k+1)) (fun i _ =>
    (pair_atom_sum i (k-i)).mul_left (A i))
  simp only [mul_one] at h
  apply h.congr_fun
  intro v
  rw [Finset.sum_eq_single v.1]
  · by_cases he : v.1+v.2=k
    · have hv : v.2=k-v.1 := by omega
      simp [weightedValuationDiagonal,A,complexAtom,hv]
    · have hv : v.2 ≠ k-v.1 := by omega
      simp [weightedValuationDiagonal,complexAtom,he,hv]
  · intro i hi hne
    simp [complexAtom,Ne.symm hne]
  · intro hv
    have hb : v.1 < -1 ∨ k-v.1 < -1 := by
      simp only [Finset.mem_Icc,not_and_or,not_le] at hv
      omega
    rcases hb with hb | hb <;> simp [A,coefficient_below z hb]

private lemma diag_neg_one (z x y : ℂ) :
    HasSum (weightedValuationDiagonal z x y (-1)) (-(z/(1-z))*(x⁻¹+y⁻¹)) := by
  have hs : Finset.Icc (-1 : ℤ) 0 = {-1,0} := by ext i; simp; omega
  have h := weightedValuationDiagonal_hasSum z x y (-1)
  norm_num only [neg_add_cancel,hs,Finset.sum_insert,Finset.sum_singleton,
    Finset.mem_singleton,neg_ne_zero,one_ne_zero,not_false_eq_true,zero_sub,
    sub_self,zpow_zero,zpow_neg_one,complexCoefficient] at h
  convert h using 1
  simp
  ring

private lemma diag_zero (z x y : ℂ) :
    HasSum (weightedValuationDiagonal z x y 0) (1-(z/(1-z))*(y/x+x/y)) := by
  have hs : Finset.Icc (-1 : ℤ) 1 = {-1,0,1} := by ext i; simp; omega
  have h := weightedValuationDiagonal_hasSum z x y 0
  simp only [zero_add,hs] at h
  norm_num [complexCoefficient] at h
  convert h using 1
  simp only [div_eq_mul_inv]
  ring

private lemma diag_one (z x y : ℂ) :
    HasSum (weightedValuationDiagonal z x y 1)
      (x+y-(z/(1-z))*(y^2/x+x^2/y)) := by
  have hs : Finset.Icc (-1 : ℤ) 2 = {-1,0,1,2} := by ext i; simp; omega
  have h := weightedValuationDiagonal_hasSum z x y 1
  norm_num [hs,complexCoefficient] at h
  simp only [zpow_ofNat] at h
  convert h using 1
  simp only [div_eq_mul_inv]
  ring

def weightedConeOffset (z x y : ℂ) (k : ℤ) (v : ℤ × ℤ) : ℂ :=
  complexCoefficient z v.1*complexCoefficient z v.2*
    complexCoefficient z (v.1+v.2+k)*x^v.1*y^v.2

private lemma coefficient_pred (z : ℂ) (i : ℤ) :
    complexCoefficient z (i-1) = complexCoefficient z i+
      z/(1-z)*complexAtom (-1) i-(1+z/(1-z))*complexAtom 0 i := by
  by_cases hi : i < -1
  · simp [coefficient_below z hi,coefficient_below z (show i-1 < -1 by omega),
      complexAtom,show i ≠ -1 by omega,show i ≠ 0 by omega]
  by_cases hi1 : i = -1
  · subst i
    norm_num [complexCoefficient,complexAtom]
    ring
  by_cases hi0 : i=0
  · subst i
    norm_num [complexCoefficient,complexAtom]
    ring
  simp [complexCoefficient,complexAtom,hi1,hi0,show 0 ≤ i by omega,
    show i-1 ≠ -1 by omega,show 1 ≤ i by omega]

theorem weightedConeOffset_pred (z x y : ℂ) (k : ℤ) (v : ℤ × ℤ) :
    weightedConeOffset z x y (k-1) v = weightedConeOffset z x y k v+
      z/(1-z)*weightedValuationDiagonal z x y (-k-1) v-
        (1+z/(1-z))*weightedValuationDiagonal z x y (-k) v := by
  unfold weightedConeOffset
  rw [show v.1+v.2+(k-1)=(v.1+v.2+k)-1 by omega,coefficient_pred]
  have h1 : v.1+v.2+k = -1 ↔ v.1+v.2 = -k-1 := by omega
  have h0 : v.1+v.2+k = 0 ↔ v.1+v.2 = -k := by omega
  simp only [complexAtom,weightedValuationDiagonal,h1,h0]
  split_ifs <;> ring

def weightedConeEulerMinusOne (z x y : ℂ) : ℂ :=
  weightedEuler z x y-(z/(1-z))^2*(x⁻¹+y⁻¹)-
    (1+z/(1-z))*(1-(z/(1-z))*(y/x+x/y))

def weightedConeEulerMinusTwo (z x y : ℂ) : ℂ :=
  weightedConeEulerMinusOne z x y+(z/(1-z))*(1-(z/(1-z))*(y/x+x/y))-
    (1+z/(1-z))*(x+y-(z/(1-z))*(y^2/x+x^2/y))

theorem weightedConeOffset_neg_one_hasSum (z : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (weightedConeOffset z x y (-1)) (weightedConeEulerMinusOne z x y) := by
  have h := ((weightedLocal_hasSum z hx hy).add ((diag_neg_one z x y).mul_left (z/(1-z)))).sub
    ((diag_zero z x y).mul_left (1+z/(1-z)))
  have he (v : ℤ × ℤ) := weightedConeOffset_pred z x y 0 v
  simp only [zero_sub,neg_zero,add_zero,weightedConeOffset] at he
  convert h.congr_fun (fun v => he v) using 1 <;> try rfl
  unfold weightedConeEulerMinusOne
  ring

theorem weightedConeOffset_neg_two_hasSum (z : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (weightedConeOffset z x y (-2)) (weightedConeEulerMinusTwo z x y) := by
  have h := ((weightedConeOffset_neg_one_hasSum z hx hy).add
    ((diag_zero z x y).mul_left (z/(1-z)))).sub
      ((diag_one z x y).mul_left (1+z/(1-z)))
  exact h.congr_fun (fun v => by simpa using weightedConeOffset_pred z x y (-1) v)

def weightedConeEuler (z x y : ℂ) (k : ℤ) : ℂ :=
  if k = -2 then weightedConeEulerMinusTwo z x y else
  if k = -1 then weightedConeEulerMinusOne z x y else
  if k = 0 then weightedEuler z x y else
    weightedEuler z x y-(z/(1-z))^3*x⁻¹*y⁻¹-
      (z/(1-z))*(1+z/(1-z))*(x⁻¹+y⁻¹)

theorem weightedConeOffset_hasSum (z : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    {k : ℤ} (hk : -2 ≤ k ∧ k ≤ 1) :
    HasSum (weightedConeOffset z x y k) (weightedConeEuler z x y k) := by
  rcases (show k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 by omega) with rfl | rfl | rfl | rfl
  · simpa [weightedConeEuler] using weightedConeOffset_neg_two_hasSum z hx hy
  · simpa [weightedConeEuler] using weightedConeOffset_neg_one_hasSum z hx hy
  · have he : weightedConeOffset z x y 0=weightedLocal z x y := by
      funext v
      simp [weightedConeOffset,weightedLocal]
    rw [he]
    simpa [weightedConeEuler] using weightedLocal_hasSum z hx hy
  · change HasSum (weightedThirdShift z x y) (weightedConeEuler z x y 1)
    simpa [weightedConeEuler] using weightedThirdShift_hasSum z hx hy

def weightedShiftedLocal (z x y : ℂ) (a b c : ℤ) (v : ℤ × ℤ) : ℂ :=
  complexCoefficient z (v.1+a)*complexCoefficient z (v.2+b)*
    complexCoefficient z (v.1+v.2+c)*x^v.1*y^v.2

theorem weightedShiftedLocal_translate (z : ℂ) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (a b c : ℤ) (v : ℤ × ℤ) :
    weightedShiftedLocal z x y a b c v = x^(-a)*y^(-b)*
      weightedConeOffset z x y (c-a-b) (v.1+a,v.2+b) := by
  have hxp : x^(-a)*x^(v.1+a)=x^v.1 := by rw [← zpow_add₀ hx]; congr 1; omega
  have hyp : y^(-b)*y^(v.2+b)=y^v.2 := by rw [← zpow_add₀ hy]; congr 1; omega
  unfold weightedShiftedLocal weightedConeOffset
  rw [show (v.1+a)+(v.2+b)+(c-a-b)=v.1+v.2+c by omega]
  calc
    _ = complexCoefficient z (v.1+a)*complexCoefficient z (v.2+b)*
        complexCoefficient z (v.1+v.2+c)*(x^(-a)*x^(v.1+a))*(y^(-b)*y^(v.2+b)) := by rw [hxp,hyp]
    _ = _ := by ring

theorem weightedShiftedLocal_hasSum (z : ℂ) {x y : ℂ} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (a b c : ℤ) (hk : -2 ≤ c-a-b ∧ c-a-b ≤ 1) :
    HasSum (weightedShiftedLocal z x y a b c)
      (x^(-a)*y^(-b)*weightedConeEuler z x y (c-a-b)) := by
  let e := (Equiv.addRight a).prodCongr (Equiv.addRight b)
  have h := (e.hasSum_iff.mpr (weightedConeOffset_hasSum z hx hy hk)).mul_left (x^(-a)*y^(-b))
  exact h.congr_fun (fun v => weightedShiftedLocal_translate z hx0 hy0 a b c v)

/-- Every distinguished-prime placement, including coinciding labels, retains
both actual complex Mellin weights without an analytic premise. -/
theorem primeWeightedShiftedLocal_hasSum (p : Nat.Primes) (τ υ : ℝ) (a b c : Fin 2) :
    let z := cubicPrimeBase p 1
    let x := cubicPrimeBase p (1+(τ : ℂ)*Complex.I)
    let y := cubicPrimeBase p (1+(υ : ℂ)*Complex.I)
    HasSum (weightedShiftedLocal z x y (a : ℕ) (b : ℕ) (c : ℕ))
      (x^(-(a : ℤ))*y^(-(b : ℤ))*weightedConeEuler z x y ((c : ℤ)-(a : ℤ)-(b : ℤ))) := by
  have hnorm (t : ℝ) : ‖cubicPrimeBase p (1+(t : ℂ)*Complex.I)‖ < 1 := by
    rw [norm_cubicPrimeBase]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt)
    simp
  apply weightedShiftedLocal_hasSum _ (cubicPrimeBase_ne_zero p _) (cubicPrimeBase_ne_zero p _)
    (hnorm τ) (hnorm υ)
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  omega

/-- The complete finite-prime signed weighted lattice for every placement. -/
theorem finitePrimeWeightedShiftedCubic_hasSum (P : Finset Nat.Primes) (τ υ : ℝ)
    (a b c : Nat.Primes → Fin 2) :
    HasSum (fun v : P → ℤ × ℤ => ∏ p : P,
      weightedShiftedLocal (cubicPrimeBase p 1)
        (cubicPrimeBase p (1+(τ : ℂ)*Complex.I))
        (cubicPrimeBase p (1+(υ : ℂ)*Complex.I)) (a p : ℕ) (b p : ℕ) (c p : ℕ) (v p))
      (∏ p : P, (cubicPrimeBase p (1+(τ : ℂ)*Complex.I))^(-(a p : ℤ))*
        (cubicPrimeBase p (1+(υ : ℂ)*Complex.I))^(-(b p : ℤ))*
          weightedConeEuler (cubicPrimeBase p 1)
            (cubicPrimeBase p (1+(τ : ℂ)*Complex.I))
            (cubicPrimeBase p (1+(υ : ℂ)*Complex.I)) ((c p : ℤ)-(a p : ℤ)-(b p : ℤ))) :=
  complex_finite_product_hasSum P _ _ (fun p => primeWeightedShiftedLocal_hasSum p τ υ (a p) (b p) (c p))

end RHTower.BAGTrace
