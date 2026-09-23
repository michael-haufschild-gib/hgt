import GaloisForLFunctions.HTGeometry.RisingFactorialPolynomial

/-!
# Expansion of a standard rational function to arbitrary depth

A *standard* rational function on the right half plane is a quotient `P(x)/∏_j (x + j)` whose
denominator is a product of factors shifted by natural numbers, with a degree defect of at least
`p` — this is exactly the shape produced by one expansion step of a polygamma jet, and the shape is
closed under the step, since subtracting a reciprocal rising factorial only appends `p` more factors.

Each step lowers the numerator degree by one, so the defect grows by one.  Iterating gives, for every
depth `K`, a finite combination of reciprocal rising factorials plus a standard remainder of defect
`p + K`.  Since the reciprocal rising factorials sum in closed form over a shift orbit and the
remainder is controlled by the orbit bound, this is the depth machinery the general residue law
needs.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- A product of factors shifted by natural numbers. -/
noncomputable def shiftProd (l : Multiset ℕ) (x : ℂ) : ℂ :=
  (Multiset.map (fun j : ℕ => x + (j : ℂ)) l).prod

/-- The same product as a polynomial. -/
noncomputable def shiftPoly (l : Multiset ℕ) : Polynomial ℂ :=
  (Multiset.map (fun j : ℕ => Polynomial.X + Polynomial.C (j : ℂ)) l).prod

@[simp] theorem shiftPoly_eval (l : Multiset ℕ) (x : ℂ) :
    (shiftPoly l).eval x = shiftProd l x := by
  induction l using Multiset.induction_on with
  | empty => simp [shiftPoly, shiftProd]
  | cons j l ih =>
    rw [shiftPoly, Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul,
      shiftProd, Multiset.map_cons, Multiset.prod_cons]
    rw [← shiftPoly, ← shiftProd, ih]
    simp

theorem shiftPoly_monic (l : Multiset ℕ) : (shiftPoly l).Monic := by
  rw [shiftPoly]
  refine Polynomial.monic_multiset_prod_of_monic _ _ fun j _ => ?_
  exact Polynomial.monic_X_add_C _

@[simp] theorem shiftPoly_natDegree (l : Multiset ℕ) :
    (shiftPoly l).natDegree = Multiset.card l := by
  induction l using Multiset.induction_on with
  | empty => simp [shiftPoly]
  | cons j l ih =>
    rw [shiftPoly, Multiset.map_cons, Multiset.prod_cons, ← shiftPoly,
      Polynomial.natDegree_mul (Polynomial.monic_X_add_C (j : ℂ)).ne_zero
        (shiftPoly_monic l).ne_zero,
      Polynomial.natDegree_X_add_C, ih, Multiset.card_cons]
    omega

theorem shiftProd_add (l m : Multiset ℕ) (x : ℂ) :
    shiftProd (l + m) x = shiftProd l x * shiftProd m x := by
  rw [shiftProd, shiftProd, shiftProd, Multiset.map_add, Multiset.prod_add]

theorem risingProd_eq_shiftProd (x : ℂ) (m : ℕ) :
    risingProd x m = shiftProd (Multiset.range m) x := by
  rw [risingProd, shiftProd]
  rfl

/-- Every factor of a shift product has modulus at least that of the argument. -/
theorem norm_pow_le_norm_shiftProd {x : ℂ} (hx : 0 < x.re) (l : Multiset ℕ) :
    ‖x‖ ^ Multiset.card l ≤ ‖shiftProd l x‖ := by
  induction l using Multiset.induction_on with
  | empty => simp [shiftProd]
  | cons j l ih =>
    rw [shiftProd, Multiset.map_cons, Multiset.prod_cons, norm_mul, ← shiftProd,
      Multiset.card_cons, pow_succ, mul_comm (‖x‖ ^ Multiset.card l) ‖x‖]
    exact mul_le_mul (norm_le_norm_add_nat hx j) ih (by positivity) (norm_nonneg _)

theorem shiftProd_ne_zero {x : ℂ} (hx : 0 < x.re) (l : Multiset ℕ) : shiftProd l x ≠ 0 := by
  intro h
  have hpos : (0 : ℝ) < ‖x‖ := by
    have : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx
      simp at hx
    positivity
  have := norm_pow_le_norm_shiftProd hx l
  rw [h, norm_zero] at this
  have hp : (0 : ℝ) < ‖x‖ ^ Multiset.card l := by positivity
  linarith

/-- **The expansion step in the standard shape.** -/
theorem shift_expansion_step (P : Polynomial ℂ) (l : Multiset ℕ) (d p : ℕ) (hp : 1 ≤ p)
    (hcard : Multiset.card l = d + p) (hdeg : P.natDegree ≤ d) :
    ∃ Q : Polynomial ℂ, Q.natDegree + 1 ≤ Multiset.card l ∧
      ∀ x : ℂ, 0 < x.re →
        P.eval x / shiftProd l x - P.coeff d * (risingProd x p)⁻¹
          = Q.eval x / (shiftProd l x * risingProd x p) := by
  classical
  set c : ℂ := P.coeff d with hc
  set Q : Polynomial ℂ := P * risingPoly p - Polynomial.C c * shiftPoly l with hQ
  have habpos : 1 ≤ Multiset.card l := by omega
  have hlow : (P - Polynomial.C c * Polynomial.X ^ d).degree < ((d : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro n hn
    rcases eq_or_lt_of_le hn with hEq | hLt
    · rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos hEq.symm,
        mul_one, ← hEq, hc]
      ring
    · have h1 : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h2 : (Polynomial.C c * Polynomial.X ^ d).coeff n = 0 := by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
      rw [Polynomial.coeff_sub, h1, h2, sub_zero]
  have hfirst : ((P - Polynomial.C c * Polynomial.X ^ d) * risingPoly p).degree
      < ((Multiset.card l : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree (risingPoly_ne_zero p),
      risingPoly_natDegree]
    have hsum : ((d : ℕ) : WithBot ℕ) + (p : ℕ) = ((Multiset.card l : ℕ) : WithBot ℕ) := by
      rw [hcard]
      push_cast
      ring
    rw [← hsum]
    exact WithBot.add_lt_add_right (by simp) hlow
  have hmon1 : (Polynomial.X ^ d * risingPoly p).Monic := monic_X_pow_mul_risingPoly d p
  have hmon2 : (shiftPoly l).Monic := shiftPoly_monic l
  have hdeg1 : (Polynomial.X ^ d * risingPoly p).natDegree = Multiset.card l := by
    rw [natDegree_X_pow_mul_risingPoly, hcard]
  have hdeg2 : (shiftPoly l).natDegree = Multiset.card l := shiftPoly_natDegree l
  have hsecond : (Polynomial.X ^ d * risingPoly p - shiftPoly l).degree
      < ((Multiset.card l : ℕ) : WithBot ℕ) := by
    have hdegeq : (Polynomial.X ^ d * risingPoly p).degree = (shiftPoly l).degree := by
      rw [Polynomial.degree_eq_natDegree hmon1.ne_zero,
        Polynomial.degree_eq_natDegree hmon2.ne_zero, hdeg1, hdeg2]
    have hlt := Polynomial.degree_sub_lt hdegeq hmon1.ne_zero
      (by rw [hmon1.leadingCoeff, hmon2.leadingCoeff])
    rwa [Polynomial.degree_eq_natDegree hmon1.ne_zero, hdeg1] at hlt
  have hsplit : Q = (P - Polynomial.C c * Polynomial.X ^ d) * risingPoly p
      + Polynomial.C c * (Polynomial.X ^ d * risingPoly p - shiftPoly l) := by
    rw [hQ]
    ring
  have hQdeg : Q.degree < ((Multiset.card l : ℕ) : WithBot ℕ) := by
    rw [hsplit]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hfirst ?_)
    refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
    have hC : (Polynomial.C c).degree ≤ 0 := Polynomial.degree_C_le
    calc (Polynomial.C c).degree + (Polynomial.X ^ d * risingPoly p - shiftPoly l).degree
        ≤ 0 + (Polynomial.X ^ d * risingPoly p - shiftPoly l).degree :=
          add_le_add hC (le_refl _)
      _ = (Polynomial.X ^ d * risingPoly p - shiftPoly l).degree := by rw [zero_add]
      _ < ((Multiset.card l : ℕ) : WithBot ℕ) := hsecond
  refine ⟨Q, ?_, fun x hx => ?_⟩
  · by_cases hQ0 : Q = 0
    · rw [hQ0]
      simpa using habpos
    · have := (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr hQdeg
      omega
  · have hxne : x ≠ 0 := by
      intro h
      rw [h] at hx
      simp at hx
    have hL : shiftProd l x ≠ 0 := shiftProd_ne_zero hx l
    have hRp : risingProd x p ≠ 0 := risingProd_ne_zero hx p
    have hQeval : Q.eval x = P.eval x * risingProd x p - c * shiftProd l x := by
      rw [hQ]
      simp
    rw [hQeval]
    field_simp

/-- A standard rational function: a quotient by a shift product with a prescribed degree defect. -/
def IsStdRat (f : ℂ → ℂ) (p : ℕ) : Prop :=
  ∃ (P : Polynomial ℂ) (l : Multiset ℕ), P.natDegree + p ≤ Multiset.card l ∧
    ∀ x : ℂ, 0 < x.re → f x = P.eval x / shiftProd l x

/-- **The decay order of a standard rational function.** -/
theorem IsStdRat.exists_norm_le {f : ℂ → ℂ} {p : ℕ} (hf : IsStdRat f p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 < x.re → 1 ≤ ‖x‖ → ‖f x‖ ≤ C * ‖x‖⁻¹ ^ p := by
  obtain ⟨P, l, hdeg, hval⟩ := hf
  obtain ⟨C, hC, hbound⟩ := exists_norm_polynomial_le P
  refine ⟨C, hC, fun x hx hx1 => ?_⟩
  have hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le zero_lt_one hx1
  have hden : ‖x‖ ^ Multiset.card l ≤ ‖shiftProd l x‖ := norm_pow_le_norm_shiftProd hx l
  have hdenpos : (0 : ℝ) < ‖shiftProd l x‖ := lt_of_lt_of_le (by positivity) hden
  rw [hval x hx, norm_div, div_le_iff₀ hdenpos]
  have hstep : C * ‖x‖ ^ P.natDegree ≤ C * ‖x‖⁻¹ ^ p * ‖x‖ ^ Multiset.card l := by
    rw [inv_pow, mul_assoc, mul_comm ((‖x‖ ^ p)⁻¹) (‖x‖ ^ Multiset.card l), ← mul_assoc]
    have hpow : ‖x‖ ^ P.natDegree ≤ ‖x‖ ^ Multiset.card l * (‖x‖ ^ p)⁻¹ := by
      rw [← pow_sub₀ _ (ne_of_gt hxpos) (by omega : p ≤ Multiset.card l)]
      exact pow_le_pow_right₀ hx1 (by omega)
    calc C * ‖x‖ ^ P.natDegree ≤ C * (‖x‖ ^ Multiset.card l * (‖x‖ ^ p)⁻¹) :=
          mul_le_mul_of_nonneg_left hpow hC
      _ = C * ‖x‖ ^ Multiset.card l * (‖x‖ ^ p)⁻¹ := by ring
  refine le_trans (hbound x hx1) (le_trans hstep ?_)
  exact mul_le_mul_of_nonneg_left hden (by positivity)

/-- **One expansion step.**  A standard rational function of defect `p ≥ 1` splits into its leading
reciprocal rising factorial and a standard remainder of defect `p + 1`. -/
theorem IsStdRat.step {f : ℂ → ℂ} {p : ℕ} (hf : IsStdRat f p) (hp : 1 ≤ p) :
    ∃ (c : ℂ) (g : ℂ → ℂ), IsStdRat g (p + 1) ∧
      ∀ x : ℂ, 0 < x.re → f x = c * (risingProd x p)⁻¹ + g x := by
  obtain ⟨P, l, hdeg, hval⟩ := hf
  obtain ⟨Q, hQdeg, hQval⟩ := shift_expansion_step P l (Multiset.card l - p) p hp
    (by omega) (by omega)
  refine ⟨P.coeff (Multiset.card l - p), fun x => Q.eval x / shiftProd (l + Multiset.range p) x,
    ⟨Q, l + Multiset.range p, ?_, fun x _ => rfl⟩, fun x hx => ?_⟩
  · rw [Multiset.card_add, Multiset.card_range]
    omega
  · have hstep := hQval x hx
    show f x = P.coeff (Multiset.card l - p) * (risingProd x p)⁻¹
      + Q.eval x / shiftProd (l + Multiset.range p) x
    rw [hval x hx, shiftProd_add, ← risingProd_eq_shiftProd]
    linear_combination hstep

/-- **The expansion to arbitrary depth.**  Iterating the step gives a finite combination of
reciprocal rising factorials plus a standard remainder of defect `p + K`. -/
theorem IsStdRat.expansion {f : ℂ → ℂ} {p : ℕ} (hf : IsStdRat f p) (hp : 1 ≤ p) (K : ℕ) :
    ∃ (c : ℕ → ℂ) (g : ℂ → ℂ), IsStdRat g (p + K) ∧
      ∀ x : ℂ, 0 < x.re →
        f x = (∑ i ∈ Finset.range K, c i * (risingProd x (p + i))⁻¹) + g x := by
  induction K with
  | zero => exact ⟨fun _ => 0, f, by simpa using hf, fun x _ => by simp⟩
  | succ K ih =>
    obtain ⟨c, g, hg, hval⟩ := ih
    obtain ⟨cK, h, hh, hgval⟩ := hg.step (le_trans hp (Nat.le_add_right p K))
    refine ⟨fun i => if i = K then cK else c i, h, ?_, fun x hx => ?_⟩
    · have : p + K + 1 = p + (K + 1) := by omega
      rwa [this] at hh
    · rw [hval x hx, hgval x hx, Finset.sum_range_succ]
      have hcongr : ∀ i ∈ Finset.range K,
          (if i = K then cK else c i) * (risingProd x (p + i))⁻¹
            = c i * (risingProd x (p + i))⁻¹ := by
        intro i hi
        rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hi))]
      rw [Finset.sum_congr rfl hcongr]
      simp only [if_pos]
      ring

theorem shiftProd_replicate_zero (k : ℕ) (x : ℂ) :
    shiftProd (Multiset.replicate k 0) x = x ^ k := by
  induction k with
  | zero => simp [shiftProd]
  | succ k ih =>
    rw [Multiset.replicate_succ, shiftProd, Multiset.map_cons, Multiset.prod_cons, ← shiftProd,
      ih, pow_succ]
    push_cast
    ring

/-- A reciprocal power is a standard rational function of the corresponding defect. -/
theorem isStdRat_inv_pow (k : ℕ) : IsStdRat (fun x : ℂ => (x ^ k)⁻¹) k := by
  refine ⟨1, Multiset.replicate k 0, ?_, fun x hx => ?_⟩
  · simp
  · rw [shiftProd_replicate_zero]
    simp

/-- A weaker defect is still a defect. -/
theorem IsStdRat.mono {f : ℂ → ℂ} {p q : ℕ} (hqp : q ≤ p) (hf : IsStdRat f p) : IsStdRat f q := by
  obtain ⟨P, l, hdeg, hval⟩ := hf
  exact ⟨P, l, by omega, hval⟩

/-- Standard rational functions are closed under multiplication, with defects adding. -/
theorem IsStdRat.mul {f g : ℂ → ℂ} {p q : ℕ} (hf : IsStdRat f p) (hg : IsStdRat g q) :
    IsStdRat (fun x => f x * g x) (p + q) := by
  obtain ⟨P, l, hdegP, hvalP⟩ := hf
  obtain ⟨R, m, hdegR, hvalR⟩ := hg
  refine ⟨P * R, l + m, ?_, fun x hx => ?_⟩
  · by_cases hP : P = 0
    · rw [hP, zero_mul]
      simp only [Polynomial.natDegree_zero]
      rw [Multiset.card_add]
      omega
    · by_cases hR : R = 0
      · rw [hR, mul_zero]
        simp only [Polynomial.natDegree_zero]
        rw [Multiset.card_add]
        omega
      · rw [Polynomial.natDegree_mul hP hR, Multiset.card_add]
        omega
  · show f x * g x = Polynomial.eval x (P * R) / shiftProd (l + m) x
    rw [hvalP x hx, hvalR x hx, Polynomial.eval_mul, shiftProd_add, div_mul_div_comm]

/-- Standard rational functions of the same defect are closed under addition. -/
theorem IsStdRat.add {f g : ℂ → ℂ} {p : ℕ} (hf : IsStdRat f p) (hg : IsStdRat g p) :
    IsStdRat (fun x => f x + g x) p := by
  obtain ⟨P, l, hdegP, hvalP⟩ := hf
  obtain ⟨R, m, hdegR, hvalR⟩ := hg
  refine ⟨P * shiftPoly m + R * shiftPoly l, l + m, ?_, fun x hx => ?_⟩
  · have h1 : (P * shiftPoly m).natDegree ≤ P.natDegree + Multiset.card m := by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [shiftPoly_natDegree]
    have h2 : (R * shiftPoly l).natDegree ≤ R.natDegree + Multiset.card l := by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [shiftPoly_natDegree]
    have h3 := Polynomial.natDegree_add_le (P * shiftPoly m) (R * shiftPoly l)
    rw [Multiset.card_add]
    omega
  · show f x + g x
        = Polynomial.eval x (P * shiftPoly m + R * shiftPoly l) / shiftProd (l + m) x
    have hL : shiftProd l x ≠ 0 := shiftProd_ne_zero hx l
    have hM : shiftProd m x ≠ 0 := shiftProd_ne_zero hx m
    rw [hvalP x hx, hvalR x hx, shiftProd_add, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, shiftPoly_eval, shiftPoly_eval]
    field_simp

/-- Scaling preserves the defect. -/
theorem IsStdRat.const_mul {f : ℂ → ℂ} {p : ℕ} (c : ℂ) (hf : IsStdRat f p) :
    IsStdRat (fun x => c * f x) p := by
  obtain ⟨P, l, hdeg, hval⟩ := hf
  refine ⟨Polynomial.C c * P, l, ?_, fun x hx => ?_⟩
  · have hCP : (Polynomial.C c * P).natDegree ≤ P.natDegree := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      simp
    omega
  · show c * f x = Polynomial.eval x (Polynomial.C c * P) / shiftProd l x
    rw [hval x hx, Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]

/-- Powers multiply the defect. -/
theorem IsStdRat.pow {f : ℂ → ℂ} {p : ℕ} (hf : IsStdRat f p) (n : ℕ) :
    IsStdRat (fun x => f x ^ n) (p * n) := by
  induction n with
  | zero =>
    refine ⟨1, 0, by simp, fun x _ => ?_⟩
    show f x ^ (0 : ℕ) = Polynomial.eval x 1 / shiftProd 0 x
    simp [shiftProd]
  | succ n ih =>
    have hmul := ih.mul hf
    have hfun : (fun x : ℂ => f x ^ n * f x) = fun x : ℂ => f x ^ (n + 1) := by
      funext x
      rw [pow_succ]
    rw [hfun] at hmul
    have hidx : p * n + p = p * (n + 1) := by ring
    rwa [hidx] at hmul

/-- The zero function is standard of every defect. -/
theorem isStdRat_zero (p : ℕ) : IsStdRat (fun _ : ℂ => (0 : ℂ)) p := by
  refine ⟨0, Multiset.replicate p 0, ?_, fun x hx => ?_⟩
  · simp
  · rw [Polynomial.eval_zero, zero_div]

/-- Finite sums of standard rational functions of a common defect are standard. -/
theorem IsStdRat.sum {ι : Type*} {p : ℕ} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, IsStdRat (f i) p) :
    IsStdRat (fun x => ∑ i ∈ s, f i x) p := by
  classical
  induction s using Finset.induction with
  | empty =>
    have := isStdRat_zero (p := p)
    refine ⟨0, Multiset.replicate p 0, by simp, fun x hx => ?_⟩
    simp
  | insert x s hx ih =>
    have hrest := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hhead := hf x (Finset.mem_insert_self x s)
    have hadd := hhead.add hrest
    have hfun : (fun y : ℂ => f x y + ∑ i ∈ s, f i y)
        = fun y : ℂ => ∑ i ∈ insert x s, f i y := by
      funext y
      rw [Finset.sum_insert hx]
    rwa [hfun] at hadd

/-- A reciprocal rising factorial is standard of its own length. -/
theorem isStdRat_inv_risingProd (q : ℕ) : IsStdRat (fun x : ℂ => (risingProd x q)⁻¹) q := by
  refine ⟨1, Multiset.range q, ?_, fun x hx => ?_⟩
  · simp
  · show (risingProd x q)⁻¹ = Polynomial.eval x 1 / shiftProd (Multiset.range q) x
    rw [risingProd_eq_shiftProd]
    simp

/-- Finite products of standard rational functions are standard, with defects adding. -/
theorem IsStdRat.prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (p : ι → ℕ)
    (hf : ∀ i ∈ s, IsStdRat (f i) (p i)) :
    IsStdRat (fun x => ∏ i ∈ s, f i x) (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨1, 0, by simp, fun x _ => ?_⟩
    show ∏ i ∈ (∅ : Finset ι), f i x = Polynomial.eval x 1 / shiftProd 0 x
    simp [shiftProd]
  | insert x s hx ih =>
    have hrest := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hhead := hf x (Finset.mem_insert_self x s)
    have hmul := hhead.mul hrest
    have hfun : (fun y : ℂ => f x y * ∏ i ∈ s, f i y)
        = fun y : ℂ => ∏ i ∈ insert x s, f i y := by
      funext y
      rw [Finset.prod_insert hx]
    rw [hfun] at hmul
    have hidx : p x + ∑ i ∈ s, p i = ∑ i ∈ insert x s, p i := by
      rw [Finset.sum_insert hx]
    rwa [hidx] at hmul

/-- A polynomial against a power of at least its degree is standard of defect zero, hence bounded on
the line.  This is the shape a polynomial coefficient takes once it is normalized. -/
theorem isStdRat_poly_div_pow (a : Polynomial ℂ) (d : ℕ) (hd : a.natDegree ≤ d) :
    IsStdRat (fun x : ℂ => a.eval x / x ^ d) 0 := by
  refine ⟨a, Multiset.replicate d 0, ?_, fun x hx => ?_⟩
  · simpa using hd
  · show a.eval x / x ^ d = a.eval x / shiftProd (Multiset.replicate d 0) x
    rw [shiftProd_replicate_zero]

end GaloisForLFunctions
