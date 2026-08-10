import GaloisForLFunctions.HTGeometry.AbelianZetaGas.KMSState

/-!
# Positivity of the Gibbs functional

The Gram kernel of the Gibbs functional has a closed form: `φ(x* y)` vanishes unless the two
monomials carry the same charge, and on that locus it is `∏_i q_i^{max(x.lower i, y.lower i)}`.
That kernel is a Hadamard product of the charge-equality kernel with one kernel per mode, and each
mode kernel is a finite nonnegative combination of rank-one kernels because
`q^{max(b,d)} = q^b q^d q^{-min(b,d)}` and `q^{-min}` telescopes with nonnegative increments.
-/

namespace GaloisForLFunctions.HTGeometry

namespace GasWord

variable {M : Type*}

/-! ## The Gram kernel in closed form -/

theorem zprod_natToInt (q : M → ℂ) (f : M →₀ ℕ) :
    zprod q (natToInt f) = f.prod fun i n => q i ^ n := by
  rw [zprod, natToInt, Finsupp.prod_mapRange_index (fun i => zpow_zero (q i))]
  exact Finsupp.prod_congr fun i _ => zpow_natCast (q i) (f i)

/-- The natural-exponent weight of a monomial. -/
noncomputable def natWeight (q : M → ℂ) (f : M →₀ ℕ) : ℂ := f.prod fun i n => q i ^ n

theorem gibbsWeight_eq_natWeight {q : M → ℂ} {x : GasWord M} (h : x.raise = x.lower) :
    gibbsWeight q x = natWeight q x.raise := by
  rw [gibbsWeight_of_diag h, zprod_natToInt, natWeight]

theorem charge_eq_iff (x y : GasWord M) :
    charge x = charge y ↔ ∀ i, (x.raise i : ℤ) - x.lower i = (y.raise i : ℤ) - y.lower i := by
  constructor
  · intro h i
    have := congrFun (congrArg (fun f : M →₀ ℤ => (f : M → ℤ)) h) i
    rwa [charge_apply, charge_apply] at this
  · intro h
    refine Finsupp.ext fun i => ?_
    rw [charge_apply, charge_apply]
    exact h i

/-- **The Gram pairing is charge-diagonal.** -/
theorem diag_wstar_mul_iff (x y : GasWord M) :
    (wstar x * y).raise = (wstar x * y).lower ↔ charge x = charge y := by
  rw [diag_iff_charge, charge_mul, charge_wstar]
  constructor
  · intro h
    have := congrArg (fun f : M →₀ ℤ => charge x + f) h
    simpa using this.symm
  · intro h
    rw [h, neg_add_cancel]

/-- **The Gram exponent is the pointwise maximum of the two lower exponents.** -/
theorem raise_wstar_mul_eq_sup {x y : GasWord M} (h : charge x = charge y) :
    (wstar x * y).raise = x.lower ⊔ y.lower := by
  refine Finsupp.ext fun i => ?_
  rw [raise_apply_mul, wstar_raise, wstar_lower, Finsupp.sup_apply]
  have hi := (charge_eq_iff x y).mp h i
  omega

open Classical in
/-- **The Gram kernel of the Gibbs functional, in closed form.** -/
theorem gibbsWeight_wstar_mul (q : M → ℂ) (x y : GasWord M) :
    gibbsWeight q (wstar x * y)
      = if charge x = charge y then natWeight q (x.lower ⊔ y.lower) else 0 := by
  classical
  by_cases h : charge x = charge y
  · rw [if_pos h, gibbsWeight_eq_natWeight ((diag_wstar_mul_iff x y).mpr h),
      raise_wstar_mul_eq_sup h]
  · rw [if_neg h, gibbsWeight_of_not_diag]
    exact fun hd => h ((diag_wstar_mul_iff x y).mp hd)

/-! ## Rank-one kernels -/

open scoped ComplexOrder

/-- **A real rank-one kernel is positive semidefinite**, in the finitely supported quadratic form
that `Matrix.PosSemidef` uses. -/
theorem quadForm_rankOne_nonneg {ι : Type*} (u : ι → ℝ) (c : ι →₀ ℂ) :
    0 ≤ (c.sum fun i ci => c.sum fun j cj =>
      star ci * (((u i : ℝ) : ℂ) * ((u j : ℝ) : ℂ)) * cj) := by
  classical
  have key : (c.sum fun i ci => c.sum fun j cj =>
        star ci * (((u i : ℝ) : ℂ) * ((u j : ℝ) : ℂ)) * cj)
      = star (∑ j ∈ c.support, ((u j : ℝ) : ℂ) * c j)
        * (∑ j ∈ c.support, ((u j : ℝ) : ℂ) * c j) := by
    rw [star_sum, Finset.sum_mul_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hstar : star (((u i : ℝ) : ℂ) * c i) = ((u i : ℝ) : ℂ) * star (c i) := by
      rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [hstar]
    ring
  rw [key]
  exact star_mul_self_nonneg _

/-! ## The telescoping decomposition of one mode -/

/-- The telescoping coefficients of `q^{-m}`. -/
noncomputable def telCoeff (t : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else (t⁻¹) ^ k * (1 - t)

theorem telCoeff_nonneg {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (k : ℕ) : 0 ≤ telCoeff t k := by
  rw [telCoeff]
  split
  · norm_num
  · have h1 : (0 : ℝ) < t⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ 1 - t := by linarith
    positivity

theorem sum_telCoeff {t : ℝ} (ht0 : 0 < t) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), telCoeff t k = (t⁻¹) ^ m := by
  have ht : t ≠ 0 := ne_of_gt ht0
  induction m with
  | zero => simp [telCoeff]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, telCoeff, if_neg (Nat.succ_ne_zero n)]
    have hkey : t⁻¹ ^ (n + 1) * t = t⁻¹ ^ n := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ ht, mul_one]
    linear_combination -hkey

theorem pow_mul_pow_mul_inv_pow_min {t : ℝ} (ht0 : 0 < t) (b d : ℕ) :
    t ^ b * t ^ d * (t⁻¹) ^ (min b d) = t ^ (max b d) := by
  have ht : t ≠ 0 := ne_of_gt ht0
  have hbd : b + d = max b d + min b d := by omega
  rw [← pow_add, hbd, pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ ht, one_pow, mul_one]

/-- The rank-one vectors of the mode decomposition. -/
noncomputable def modeVec (t : ℝ) (k b : ℕ) : ℝ := if k ≤ b then t ^ b else 0

/-- **The single-mode kernel `t^{max(b,d)}` is a nonnegative combination of rank-one kernels.** -/
theorem modeKernel_decomp {t : ℝ} (ht0 : 0 < t) {b d N : ℕ} (hb : b ≤ N) :
    ∑ k ∈ Finset.range (N + 1), telCoeff t k * modeVec t k b * modeVec t k d
      = t ^ (max b d) := by
  classical
  have hminN : min b d ≤ N := le_trans (min_le_left b d) hb
  have hsub : Finset.range (min b d + 1) ⊆ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have hvanish : ∀ k ∈ Finset.range (N + 1), k ∉ Finset.range (min b d + 1) →
      telCoeff t k * modeVec t k b * modeVec t k d = 0 := by
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rcases min_choice b d with h | h
    · have hk' : b + 1 ≤ k := by rw [← h]; exact hk
      have hkb : ¬ k ≤ b := by omega
      simp [modeVec, hkb]
    · have hk' : d + 1 ≤ k := by rw [← h]; exact hk
      have hkd : ¬ k ≤ d := by omega
      simp [modeVec, hkd]
  rw [← Finset.sum_subset hsub hvanish]
  have hval : ∀ k ∈ Finset.range (min b d + 1),
      telCoeff t k * modeVec t k b * modeVec t k d = telCoeff t k * (t ^ b * t ^ d) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : k ≤ b := by omega
    have h2 : k ≤ d := by omega
    rw [modeVec, modeVec, if_pos h1, if_pos h2]
    ring
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, sum_telCoeff ht0,
    ← pow_mul_pow_mul_inv_pow_min ht0 b d]
  ring

/-! ## Quadratic forms with a rank-one decomposition -/

/-- **A kernel that is a sum of real rank-one kernels on a finite set has a nonnegative quadratic
form there.** -/
theorem quadForm_nonneg_of_decomp {ι κ : Type*} (K : Matrix ι ι ℂ) (c : ι →₀ ℂ)
    (s : Finset κ) (u : κ → ι → ℝ)
    (h : ∀ x ∈ c.support, ∀ y ∈ c.support,
      K x y = ∑ k ∈ s, ((u k x : ℝ) : ℂ) * ((u k y : ℝ) : ℂ)) :
    0 ≤ c.sum fun i ci => c.sum fun j cj => star ci * K i j * cj := by
  classical
  have hrw : (c.sum fun i ci => c.sum fun j cj => star ci * K i j * cj)
      = ∑ k ∈ s, (c.sum fun i ci => c.sum fun j cj =>
          star ci * (((u k i : ℝ) : ℂ) * ((u k j : ℝ) : ℂ)) * cj) := by
    simp only [Finsupp.sum]
    have step1 : ∀ i ∈ c.support, (∑ j ∈ c.support, star (c i) * K i j * c j)
        = ∑ k ∈ s, ∑ j ∈ c.support,
            star (c i) * (((u k i : ℝ) : ℂ) * ((u k j : ℝ) : ℂ)) * c j := by
      intro i hi
      have hterm : ∀ j ∈ c.support, star (c i) * K i j * c j
          = ∑ k ∈ s, star (c i) * (((u k i : ℝ) : ℂ) * ((u k j : ℝ) : ℂ)) * c j := by
        intro j hj
        rw [h i hi j hj, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  rw [hrw]
  exact Finset.sum_nonneg fun k _ => quadForm_rankOne_nonneg (u k) c

theorem quadForm_congr {ι : Type*} {K K' : Matrix ι ι ℂ} (c : ι →₀ ℂ)
    (h : ∀ x ∈ c.support, ∀ y ∈ c.support, K x y = K' x y) :
    (c.sum fun i ci => c.sum fun j cj => star ci * K i j * cj)
      = c.sum fun i ci => c.sum fun j cj => star ci * K' i j * cj := by
  classical
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h i hi j hj]

/-! ## The charge kernel -/

open Classical in
/-- The charge-equality kernel. -/
noncomputable def chargeKernel (M : Type*) : Matrix (GasWord M) (GasWord M) ℂ :=
  Matrix.of fun x y => if charge x = charge y then 1 else 0

open Classical in
theorem chargeKernel_apply (x y : GasWord M) :
    chargeKernel M x y = if charge x = charge y then 1 else 0 := rfl

theorem chargeKernel_posSemidef : (chargeKernel M).PosSemidef := by
  classical
  constructor
  · refine Matrix.IsHermitian.ext fun x y => ?_
    rw [chargeKernel_apply, chargeKernel_apply]
    by_cases h : charge y = charge x
    · rw [if_pos h, if_pos h.symm, star_one]
    · rw [if_neg h, if_neg (fun hc => h hc.symm), star_zero]
  · intro c
    refine quadForm_nonneg_of_decomp _ c (c.support.image charge)
      (fun γ x => if charge x = γ then 1 else 0) ?_
    intro x hx y hy
    rw [chargeKernel_apply]
    have hmem : charge x ∈ c.support.image charge := Finset.mem_image_of_mem _ hx
    rw [Finset.sum_eq_single (charge x)]
    · by_cases h : charge x = charge y
      · rw [if_pos h, if_pos (rfl : charge x = charge x), if_pos h.symm]
        norm_num
      · rw [if_neg h, if_pos (rfl : charge x = charge x),
          if_neg (show ¬ charge y = charge x from fun hc => h hc.symm)]
        norm_num
    · intro γ _ hγ
      rw [if_neg (fun hc => hγ hc.symm)]
      norm_num
    · intro hcon
      exact absurd hmem hcon

/-! ## The single-mode kernel -/

/-- The kernel of one mode. -/
noncomputable def modeKernel (t : ℝ) (i : M) : Matrix (GasWord M) (GasWord M) ℂ :=
  Matrix.of fun x y => ((t : ℂ)) ^ (max (x.lower i) (y.lower i))

theorem modeKernel_posSemidef {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (i : M) :
    (modeKernel (M := M) t i).PosSemidef := by
  classical
  constructor
  · refine Matrix.IsHermitian.ext fun x y => ?_
    show star (((t : ℂ)) ^ (max (y.lower i) (x.lower i)))
      = ((t : ℂ)) ^ (max (x.lower i) (y.lower i))
    rw [max_comm, ← Complex.ofReal_pow, Complex.star_def, Complex.conj_ofReal]
  · intro c
    refine quadForm_nonneg_of_decomp _ c (Finset.range (c.support.sup (fun x => x.lower i) + 1))
      (fun k x => Real.sqrt (telCoeff t k) * modeVec t k (x.lower i)) ?_
    intro x hx y hy
    have hxN : x.lower i ≤ c.support.sup (fun x => x.lower i) :=
      Finset.le_sup (f := fun x : GasWord M => x.lower i) hx
    have hreal : ∑ k ∈ Finset.range (c.support.sup (fun x => x.lower i) + 1),
        (Real.sqrt (telCoeff t k) * modeVec t k (x.lower i))
          * (Real.sqrt (telCoeff t k) * modeVec t k (y.lower i))
        = t ^ (max (x.lower i) (y.lower i)) := by
      rw [← modeKernel_decomp ht0 hxN]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsq := Real.mul_self_sqrt (telCoeff_nonneg ht0 ht1 k)
      linear_combination (modeVec t k (x.lower i) * modeVec t k (y.lower i)) * hsq
    show ((t : ℂ)) ^ (max (x.lower i) (y.lower i)) = _
    rw [← Complex.ofReal_pow, ← hreal]
    push_cast
    ring

/-! ## The product over a finite set of modes -/

/-- The product of the mode kernels over a finite set of modes. -/
noncomputable def modeProd (t : M → ℝ) (T : Finset M) : Matrix (GasWord M) (GasWord M) ℂ :=
  Matrix.of fun x y => ∏ i ∈ T, ((t i : ℂ)) ^ (max (x.lower i) (y.lower i))

theorem posSemidef_ones : (Matrix.of (fun (_ : GasWord M) (_ : GasWord M) => (1 : ℂ))).PosSemidef := by
  classical
  constructor
  · exact Matrix.IsHermitian.ext fun _ _ => star_one ℂ
  · intro c
    refine quadForm_nonneg_of_decomp _ c (Finset.univ : Finset Unit) (fun _ _ => (1 : ℝ)) ?_
    intro x _ y _
    simp

theorem modeProd_empty (t : M → ℝ) :
    modeProd t (∅ : Finset M) = Matrix.of (fun (_ : GasWord M) (_ : GasWord M) => (1 : ℂ)) := by
  ext x y
  simp [modeProd]

theorem modeProd_insert [DecidableEq M] (t : M → ℝ) {i : M} {T : Finset M} (hi : i ∉ T) :
    modeProd t (insert i T) = Matrix.hadamard (modeKernel (t i) i) (modeProd t T) := by
  ext x y
  show ∏ j ∈ insert i T, _ = _
  rw [Finset.prod_insert hi]
  rfl

theorem modeProd_posSemidef [DecidableEq M] {t : M → ℝ} (ht0 : ∀ i, 0 < t i) (ht1 : ∀ i, t i < 1)
    (T : Finset M) : (modeProd (M := M) t T).PosSemidef := by
  classical
  induction T using Finset.induction with
  | empty =>
    rw [modeProd_empty]
    exact posSemidef_ones
  | insert i T hi ih =>
    rw [modeProd_insert t hi]
    exact (modeKernel_posSemidef (ht0 i) (ht1 i) i).hadamard ih

/-! ## The Gram kernel of the Gibbs functional -/

theorem support_sup_subset {f g : M →₀ ℕ} {T : Finset M} (hf : f.support ⊆ T)
    (hg : g.support ⊆ T) : (f ⊔ g).support ⊆ T := by
  intro i hi
  rw [Finsupp.mem_support_iff, Finsupp.sup_apply] at hi
  by_cases hfi : f i = 0
  · refine hg ?_
    rw [Finsupp.mem_support_iff]
    intro hgi
    exact hi (by rw [hfi, hgi]; simp)
  · exact hf (Finsupp.mem_support_iff.mpr hfi)

/-- The Gram kernel of the Gibbs functional on monomials. -/
noncomputable def gramKernel (t : M → ℝ) : Matrix (GasWord M) (GasWord M) ℂ :=
  Matrix.of fun x y => gibbsWeight (fun i => ((t i : ℝ) : ℂ)) (wstar x * y)

open Classical in
/-- **On any finite set of monomials the Gram kernel is the Hadamard product of the charge kernel
with finitely many mode kernels.** -/
theorem gramKernel_eq_on [DecidableEq M] (t : M → ℝ) {s : Finset (GasWord M)}
    {T : Finset M} (hT : ∀ x ∈ s, x.lower.support ⊆ T) :
    ∀ x ∈ s, ∀ y ∈ s,
      gramKernel t x y = Matrix.hadamard (chargeKernel M) (modeProd t T) x y := by
  intro x hx y hy
  show gibbsWeight (fun i => ((t i : ℝ) : ℂ)) (wstar x * y)
    = (chargeKernel M x y) * (modeProd t T x y)
  rw [gibbsWeight_wstar_mul, chargeKernel_apply]
  by_cases h : charge x = charge y
  · rw [if_pos h, if_pos h, one_mul, natWeight,
      Finsupp.prod_of_support_subset _ (support_sup_subset (hT x hx) (hT y hy)) _
        (fun i _ => pow_zero _)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finsupp.sup_apply]
  · rw [if_neg h, if_neg h, zero_mul]

/-- **The Gram kernel of the Gibbs functional is positive semidefinite.** -/
theorem gramKernel_quadForm_nonneg [DecidableEq M] {t : M → ℝ} (ht0 : ∀ i, 0 < t i)
    (ht1 : ∀ i, t i < 1) (c : GasWord M →₀ ℂ) :
    0 ≤ c.sum fun i ci => c.sum fun j cj => star ci * gramKernel t i j * cj := by
  classical
  have hsub : ∀ x ∈ c.support, x.lower.support
      ⊆ c.support.biUnion (fun x : GasWord M => x.lower.support) := by
    intro x hx
    exact Finset.subset_biUnion_of_mem (fun x : GasWord M => x.lower.support) hx
  rw [quadForm_congr c (gramKernel_eq_on t hsub)]
  exact ((chargeKernel_posSemidef (M := M)).hadamard
    (modeProd_posSemidef ht0 ht1 _)).2 c

end GasWord

/-! ## Positivity of the gas Gibbs functional -/

open scoped ComplexOrder

open GasWord in
/-- **The Gibbs functional of the gas is positive.**  On the monomial basis of the `*`-algebra its
Gram matrix is positive semidefinite, which is exactly the statement that `φ(a^* a) ≥ 0`. -/
theorem gasGibbs_gram_nonneg (θ : AbelianZetaParameters)
    (c : GasWord AbelianZetaMode →₀ ℂ) :
    0 ≤ c.sum fun x cx => c.sum fun y cy =>
      star cx * gasGibbs θ (MonoidAlgebra.single (wstar x * y) (1 : ℂ)) * cy := by
  have hval : ∀ x y : GasWord AbelianZetaMode,
      gasGibbs θ (MonoidAlgebra.single (wstar x * y) (1 : ℂ))
        = gramKernel (fun i => θ.ratio i) x y := by
    intro x y
    rw [gasGibbs, gibbs_single, one_mul]
    rfl
  simp only [hval]
  exact gramKernel_quadForm_nonneg (fun i => θ.ratio_pos i) (fun i => θ.ratio_lt_one i) c

/-! ## The adjoint on the algebra -/

open GasWord in
/-- The adjoint of an element of the gas algebra. -/
noncomputable def gasAdjoint {M : Type*} (a : GasAlgebra M) : GasAlgebra M :=
  MonoidAlgebra.ofCoeff (Finsupp.mapDomain wstar
    (Finsupp.mapRange (starRingEnd ℂ) (by simp) a.coeff))

open GasWord in
theorem coeff_gasAdjoint {M : Type*} (a : GasAlgebra M) :
    (gasAdjoint a).coeff = Finsupp.mapDomain wstar
      (Finsupp.mapRange (starRingEnd ℂ) (by simp) a.coeff) := rfl

open GasWord in
/-- **The Gram expansion of `φ(a^* a)`.** -/
theorem gibbs_gasAdjoint_mul_self {M : Type*} (q : M → ℂ) (a : GasAlgebra M) :
    gibbs q (gasAdjoint a * a)
      = a.coeff.sum fun x cx => a.coeff.sum fun y cy =>
          star cx * gibbsWeight q (wstar x * y) * cy := by
  classical
  rw [MonoidAlgebra.mul_def, coeff_gasAdjoint,
    Finsupp.sum_mapDomain_index_inj wstar_injective,
    Finsupp.sum_mapRange_index (by intro m; simp)]
  simp only [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [gibbs_single, Complex.star_def]
  ring

open GasWord in
/-- **Theorem 4.1, positivity.**  The Gibbs functional of the gas is a positive functional on the
monomial `*`-algebra: `φ(a^* a) ≥ 0` for every `a`. -/
theorem gasGibbs_adjoint_mul_self_nonneg (θ : AbelianZetaParameters)
    (a : GasAlgebra AbelianZetaMode) :
    0 ≤ gasGibbs θ (gasAdjoint a * a) := by
  rw [gasGibbs, gibbs_gasAdjoint_mul_self]
  have hval : ∀ x y : GasWord AbelianZetaMode,
      gibbsWeight (gasNome θ) (wstar x * y) = gramKernel (fun i => θ.ratio i) x y := fun _ _ => rfl
  simp only [hval]
  exact gramKernel_quadForm_nonneg (fun i => θ.ratio_pos i) (fun i => θ.ratio_lt_one i) a.coeff

end GaloisForLFunctions.HTGeometry
