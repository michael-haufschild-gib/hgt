import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerSuccessorForcesTheHeckeWeight

/-!
# The Bost–Connes temperature is the Hecke exponent

A positive-definite function `φ` on `Aff(ℚ)` whose successor part `ψ(b) = φ(x ↦ x + b)` is
`ℤ`-periodic has, at every level `q`, the **successor density**
`A_φ(q) = q⁻² Σ_{j,k<q} ψ((k − j)/q) ≥ 0`, the mass of `qẐ` under the spectral measure of `ψ`.

* **Successor law** (`normSq_dilation_le_successorDensity`). For `u = ±n/d` in lowest terms,
  `|φ(x ↦ ux)|² ≤ A_φ(n)·A_φ(d)`. The averages `X = d⁻¹Σ_{j<d}[x + j/d]` and
  `Y = n⁻¹Σ_{k<n}[ux + k/d]` have Gram entries `A_φ(d)`, `A_φ(n)` and `φ(x ↦ ux)`; the
  `(1/d)ℤ`-periodicity of `b ↦ φ(ux + b)` collapses the cross term. For the integer successor
  `A(q) = 1/q` and this is the Hecke weight (`normSq_dilation_le`).
* **The Bost–Connes successors** (`successorDensity_bcSuccessor`). For `β > 1` the successor
  `ψ_β(b) = Z_β⁻¹ Σ_{m≥1} m^{−β} e(mb)` of the Bost–Connes state at inverse temperature `β` has
  `A(q) = q^{−β}`: its spectral measure gives `qẐ` the mass `q^{−β}`. Hence
  `|φ(x ↦ ux)| ≤ (nd)^{−β/2}`: the temperature `β` forces the Hecke exponent `β/2`.
* **Sharpness: the ground state** (`isPosDefOnGroup_bcState`, `bc_successor_hecke_exponent`). The
  coefficient of `ξ_β = Σ_{m≥1}(m^{−β}/Z_β)^{1/2}δ_m ∈ ℓ²(ℚ)` under `π(x ↦ ax + b)v(y) = e(by)v(ay)`
  is `φ_β(x ↦ ax + b) = 1[a > 0]·(nd)^{−β/2}·ψ_β(db)`: positive definite, successor `ψ_β`, and
  equality in the law at every positive dilation.

At `β = 1` the spectral measure of the successor is Haar measure of `Ẑ`, `A(q) = 1/q`, and the law
is the Hecke weight of the integer successor; the ground state then leaves `ℓ²(ℚ)` (`Z_1 = ∞`) and
becomes the adelic Haar state. The Bost–Connes critical temperature is the critical line.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The **successor density** at level `q`: `A_φ(q) = q⁻² Σ_{j,k<q} φ(x ↦ x + (k − j)/q)`. -/
def successorDensity (φ : AffineGroupQ → ℂ) (q : ℕ) : ℂ :=
  (1 / (q : ℂ) ^ 2) * ∑ j : Fin q, ∑ k : Fin q,
    φ (translation ((((k : ℕ) : ℚ) - (j : ℕ)) / q))

/-- Periodicity of the successor-twisted dilation coefficients for an integer-periodic successor. -/
theorem tdil_periodic_of_int {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hper : ∀ m : ℤ, φ (translation m) = φ 1) (u : ℚˣ) (b : ℚ) (q : ℤ) :
    φ (translation (b + q / (u : ℚ).den) * dilation u) = φ (translation b * dilation u) := by
  have hcop : Int.gcd (u : ℚ).num ((u : ℚ).den : ℤ) = 1 := (u : ℚ).reduced
  have hbez := Int.gcd_eq_gcd_ab (u : ℚ).num ((u : ℚ).den : ℤ)
  rw [hcop] at hbez
  set x := Int.gcdA (u : ℚ).num ((u : ℚ).den : ℤ)
  set y := Int.gcdB (u : ℚ).num ((u : ℚ).den : ℤ)
  have hd : ((u : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (u : ℚ).den_ne_zero
  have hnum : ((u : ℚ).num : ℚ) = u * (u : ℚ).den := (Rat.mul_den_eq_num (u : ℚ)).symm
  have key : b + q / (u : ℚ).den = b + ((q * y : ℤ) : ℚ) + u * ((q * x : ℤ) : ℚ) := by
    have hb' : (1 : ℚ) = (u : ℚ).num * x + (u : ℚ).den * y := by exact_mod_cast hbez
    rw [hnum] at hb'
    have h1 : (q : ℚ) / (u : ℚ).den = q * y + u * (q * x) := by
      rw [div_eq_iff hd]; linear_combination (q : ℚ) * hb'
    push_cast
    rw [h1]; ring
  rw [key, translation_add_mul_dil, hφ.mul_right_eq (hper _), hφ.mul_left_eq (hper _)]

/-- **The successor law.** If `φ` is positive definite on `Aff(ℚ)` with integer-periodic successor,
then `|φ(x ↦ ux)|² ≤ A_φ(n)·A_φ(d)` for `u = ±n/d` in lowest terms. -/
theorem normSq_dilation_le_successorDensity {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hper : ∀ m : ℤ, φ (translation m) = φ 1) (u : ℚˣ) :
    Complex.normSq (φ (dilation u)) ≤
      (successorDensity φ (u : ℚ).num.natAbs).re * (successorDensity φ (u : ℚ).den).re := by
  set n := (u : ℚ).num.natAbs with hn_def
  set d := (u : ℚ).den with hd_def
  have hd : 0 < d := (u : ℚ).den_pos
  have hn : 0 < n := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hu0 : (u : ℚ) ≠ 0 := u.ne_zero
  have hnum : ((u : ℚ).num : ℚ) = u * d := (Rat.mul_den_eq_num (u : ℚ)).symm
  have hinv : ∀ x, φ x⁻¹ = star (φ x) := hφ.map_inv
  set F := φ (dilation u) with hF
  set Ad := successorDensity φ d with hAd
  set An := successorDensity φ n with hAn
  set P : Fin d ⊕ Fin n → AffineGroupQ :=
    Sum.elim (fun j => translation (((j : ℕ) : ℚ) / d))
      (fun k => translation (((k : ℕ) : ℚ) / d) * dilation u) with hP
  -- the Gram values
  have v1 : ∀ j j' : Fin d, φ ((P (Sum.inl j))⁻¹ * P (Sum.inl j')) =
      φ (translation ((((j' : ℕ) : ℚ) - (j : ℕ)) / d)) := by
    intro j j'
    simp only [hP, Sum.elim_inl, translation_inv_mul]
    congr 2; ring
  have v2 : ∀ (j : Fin d) (k : Fin n), φ ((P (Sum.inl j))⁻¹ * P (Sum.inr k)) = F := by
    intro j k
    simp only [hP, Sum.elim_inl, Sum.elim_inr, translation_inv_mul_tdil]
    have := tdil_periodic_of_int hφ hper u 0 ((k : ℕ) - (j : ℕ) : ℤ)
    rw [zero_add, translation_zero, one_mul] at this
    rw [show ((k : ℕ) : ℚ) / d - ((j : ℕ) : ℚ) / d = (((k : ℕ) - (j : ℕ) : ℤ) : ℚ) / (u : ℚ).den by
      push_cast; ring]
    exact this
  have v3 : ∀ (k : Fin n) (j : Fin d), φ ((P (Sum.inr k))⁻¹ * P (Sum.inl j)) = star F := by
    intro k j
    rw [← v2 j k, ← hinv, mul_inv_rev, inv_inv]
  have hsgn : ∀ k k' : Fin n, ((((k' : ℕ) : ℚ) / d - ((k : ℕ) : ℚ) / d) / u) =
      ((u : ℚ).num.sign : ℚ) * ((((k' : ℕ) : ℚ) - (k : ℕ)) / n) := by
    intro k k'
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hstep : (((k' : ℕ) : ℚ) / d - ((k : ℕ) : ℚ) / d) / u =
        (((k' : ℕ) : ℚ) - (k : ℕ)) / ((u : ℚ).num : ℚ) := by
      rw [hnum]; field_simp
    rw [hstep]
    rcases lt_or_gt_of_ne (Rat.num_ne_zero.mpr hu0) with h | h
    · have e : ((u : ℚ).num : ℚ) = -(n : ℚ) := by
        rw [hn_def, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]; ring
      rw [Int.sign_eq_neg_one_of_neg h, e]; push_cast; field_simp
    · have e : ((u : ℚ).num : ℚ) = (n : ℚ) := by
        rw [hn_def, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast h)]
      rw [Int.sign_eq_one_of_pos h, e]; push_cast; ring
  have v4sum : ∑ k : Fin n, ∑ k' : Fin n, φ ((P (Sum.inr k))⁻¹ * P (Sum.inr k')) =
      ∑ j : Fin n, ∑ k : Fin n, φ (translation ((((k : ℕ) : ℚ) - (j : ℕ)) / n)) := by
    simp only [hP, Sum.elim_inr, tdil_inv_mul_tdil, hsgn]
    rcases lt_or_gt_of_ne (Rat.num_ne_zero.mpr hu0) with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      congr 2; push_cast; ring
    · rw [Int.sign_eq_one_of_pos h]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      congr 2; push_cast; ring
  -- the two-vector Gram form
  have gram : ∀ α β : ℂ, ∃ r : ℝ, 0 ≤ r ∧
      star α * α * Ad + star β * β * An + star α * β * F + star β * α * star F = r := by
    intro α β
    set C : Fin d ⊕ Fin n → ℂ := Sum.elim (fun _ => α / d) (fun _ => β / n) with hC
    obtain ⟨r, hr, hsum⟩ := hφ.form P C
    refine ⟨r, hr, ?_⟩
    rw [← hsum, Fintype.sum_sum_type]
    simp only [Fintype.sum_sum_type, hC, Sum.elim_inl, Sum.elim_inr, v1, v2, v3,
      Finset.sum_add_distrib]
    have hs1 : star (α / d) = star α / d := by rw [star_div₀, star_natCast]
    have hs2 : star (β / n) = star β / n := by rw [star_div₀, star_natCast]
    rw [hs1, hs2]
    have eXX : ∑ j : Fin d, ∑ j' : Fin d, star α / d * φ (translation ((((j' : ℕ) : ℚ) - (j : ℕ)) / d)) * (α / d)
        = star α * α * Ad := by
      rw [hAd, successorDensity, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      field_simp
    have eYY : ∑ k : Fin n, ∑ k' : Fin n, star β / n * φ ((P (Sum.inr k))⁻¹ * P (Sum.inr k')) * (β / n)
        = star β * β * An := by
      have : ∑ k : Fin n, ∑ k' : Fin n, star β / n * φ ((P (Sum.inr k))⁻¹ * P (Sum.inr k')) * (β / n)
          = star β * β / n ^ 2 * ∑ k : Fin n, ∑ k' : Fin n, φ ((P (Sum.inr k))⁻¹ * P (Sum.inr k')) := by
        rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
        field_simp
      rw [this, v4sum, hAn, successorDensity]
      field_simp
    have eXY : ∑ j : Fin d, ∑ k : Fin n, star α / d * F * (β / n) = star α * β * F := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have eYX : ∑ k : Fin n, ∑ j : Fin d, star β / n * star F * (α / d) = star β * α * star F := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [eXX, eXY, eYX, eYY]
    ring
  -- reality and nonnegativity of the densities
  obtain ⟨rd, hrd, hd'⟩ := gram 1 0
  obtain ⟨rn, hrn, hn'⟩ := gram 0 1
  simp only [star_one, one_mul, star_zero, zero_mul, add_zero, zero_add, mul_zero] at hd' hn'
  rw [hd', hn', Complex.ofReal_re, Complex.ofReal_re]
  have hFF : F * star F = (Complex.normSq F : ℂ) := by rw [Complex.star_def, Complex.mul_conj]
  rcases hrn.lt_or_eq with hpos | hzero
  · obtain ⟨r, hr, h⟩ := gram (rn : ℂ) (-star F)
    have hst : star (rn : ℂ) = rn := Complex.conj_ofReal rn
    rw [hd', hn', star_neg, star_star, hst] at h
    have e : (rn : ℂ) * rn * rd + -F * -star F * rn + rn * -star F * F + -F * rn * star F =
        ((rd * rn ^ 2 - rn * Complex.normSq F : ℝ) : ℂ) := by
      push_cast
      linear_combination (-(rn : ℂ)) * hFF
    rw [e] at h
    have h' := Complex.ofReal_injective h
    have h3 : 0 ≤ rn * (rn * rd - Complex.normSq F) := by
      rw [show rn * (rn * rd - Complex.normSq F) = rd * rn ^ 2 - rn * Complex.normSq F by ring, h']
      exact hr
    have := (mul_nonneg_iff_of_pos_left hpos).mp h3
    linarith
  · have hF0 : F = 0 := by
      refine eq_zero_of_forall_quadratic (a := rd) fun t => ?_
      obtain ⟨r, hr, h⟩ := gram 1 t
      refine ⟨r, hr, ?_⟩
      rw [← h, hd', hn', ← hzero, star_mul']
      simp only [star_one, one_mul, Complex.ofReal_zero, mul_zero, add_zero, mul_one]
    rw [hF0, Complex.normSq_zero]
    exact mul_nonneg hrn hrd

/-! ### The Bost–Connes successors -/

/-- The additive character `e(x) = exp(2πix)` of `ℚ`. -/
def addChar (x : ℚ) : ℂ := Complex.exp (2 * Real.pi * I * (x : ℂ))

theorem addChar_add (x y : ℚ) : addChar (x + y) = addChar x * addChar y := by
  unfold addChar; push_cast; rw [mul_add, Complex.exp_add]

theorem addChar_int (m : ℤ) : addChar m = 1 := by
  unfold addChar
  rw [Complex.exp_eq_one_iff]
  exact ⟨m, by push_cast; ring⟩

theorem addChar_neg (x : ℚ) : addChar (-x) = star (addChar x) := by
  unfold addChar
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_ratCast]
  push_cast; ring

/-- The Bost–Connes partition function `Z_β = Σ_{m ≥ 1} m^{−β}`. -/
def bcPartition (β : ℝ) : ℝ := ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) ^ (-β)

theorem summable_bcWeight {β : ℝ} (hβ : 1 < β) :
    Summable fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-β) := by
  have h := (Real.summable_nat_rpow_inv.mpr hβ).comp_injective (add_left_injective 1)
  refine h.congr fun m => ?_
  simp only [Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg _)]

theorem bcPartition_pos {β : ℝ} (hβ : 1 < β) : 0 < bcPartition β := by
  have h := summable_bcWeight hβ
  refine lt_of_lt_of_le ?_ (h.le_tsum 0 fun m _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simp

/-- The **Bost–Connes successor** at inverse temperature `β > 1`:
`ψ_β(b) = Z_β⁻¹ Σ_{m ≥ 1} m^{−β} e(mb)`, the restriction to `ℚ/ℤ` of the KMS state. -/
def bcSuccessor (β : ℝ) (b : ℚ) : ℂ :=
  ((bcPartition β)⁻¹ : ℝ) * ∑' m : ℕ, (((m + 1 : ℕ) : ℝ) ^ (-β) : ℝ) * addChar ((m + 1 : ℕ) * b)

/-- The geometric sum of a root of unity: `Σ_{k<q} e(mk/q) = q·1[q ∣ m]`. -/
theorem sum_addChar_div (q : ℕ) (hq : 0 < q) (m : ℕ) :
    ∑ k : Fin q, addChar ((m : ℚ) * (k : ℕ) / q) = if q ∣ m then (q : ℂ) else 0 := by
  set x := addChar ((m : ℚ) / q) with hx
  have hpow : ∀ k : ℕ, addChar ((m : ℚ) * k / q) = x ^ k := by
    intro k
    rw [hx, addChar, addChar, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [Fin.sum_univ_eq_sum_range (fun k => addChar ((m : ℚ) * k / q)) q]
  simp_rw [hpow]
  split_ifs with hdvd
  · obtain ⟨t, rfl⟩ := hdvd
    have hx1 : x = 1 := by
      rw [hx, show ((q * t : ℕ) : ℚ) / q = ((t : ℤ) : ℚ) by
        push_cast; field_simp]
      exact addChar_int t
    simp [hx1]
  · have hx1 : x ≠ 1 := by
      intro h1
      rw [hx, addChar, Complex.exp_eq_one_iff] at h1
      obtain ⟨t, ht⟩ := h1
      apply hdvd
      have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
      have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have : (m : ℂ) = t * q := by
        have := ht; push_cast at this
        field_simp at this
        linear_combination this
      have hmz : (m : ℤ) = t * q := by exact_mod_cast this
      exact Int.natCast_dvd_natCast.mp ⟨t, by rw [hmz]; ring⟩
    have hxq : x ^ q = 1 := by
      rw [← hpow q, show (m : ℚ) * q / q = ((m : ℤ) : ℚ) by
        push_cast; field_simp]
      exact addChar_int m
    rw [geom_sum_eq hx1, hxq, sub_self, zero_div]

theorem norm_addChar (x : ℚ) : ‖addChar x‖ = 1 := by
  rw [addChar, show (2 * (Real.pi : ℂ) * I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- The double character sum `Σ_{j,k<q} e(m(k − j)/q) = q²·1[q ∣ m]`. -/
theorem sum_sum_addChar (q : ℕ) (hq : 0 < q) (m : ℕ) :
    ∑ j : Fin q, ∑ k : Fin q, addChar ((m : ℚ) * ((((k : ℕ) : ℚ) - (j : ℕ)) / q)) =
      if q ∣ m then (q : ℂ) ^ 2 else 0 := by
  have hsplit : ∀ j k : Fin q, addChar ((m : ℚ) * ((((k : ℕ) : ℚ) - (j : ℕ)) / q)) =
      addChar ((m : ℚ) * (k : ℕ) / q) * star (addChar ((m : ℚ) * (j : ℕ) / q)) := by
    intro j k
    rw [← addChar_neg, ← addChar_add]; congr 1; ring
  simp_rw [hsplit]
  rw [show (∑ j : Fin q, ∑ k : Fin q, addChar ((m : ℚ) * (k : ℕ) / q) *
      star (addChar ((m : ℚ) * (j : ℕ) / q))) =
      (∑ k : Fin q, addChar ((m : ℚ) * (k : ℕ) / q)) *
        star (∑ j : Fin q, addChar ((m : ℚ) * (j : ℕ) / q)) by
    rw [star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]]
  rw [sum_addChar_div q hq m]
  split_ifs <;> simp [sq]

/-- **Divisibility densities of the Bost–Connes successor**: `A(q) = q^{−β}`. -/
theorem bcDensity {β : ℝ} (hβ : 1 < β) (q : ℕ) (hq : 0 < q) :
    (1 / (q : ℂ) ^ 2) * ∑ j : Fin q, ∑ k : Fin q,
      bcSuccessor β ((((k : ℕ) : ℚ) - (j : ℕ)) / q) = (((q : ℝ) ^ (-β) : ℝ) : ℂ) := by
  set w : ℕ → ℝ := fun m => ((m + 1 : ℕ) : ℝ) ^ (-β) with hw
  have hws : Summable w := summable_bcWeight hβ
  have hZ := bcPartition_pos hβ
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsum : ∀ x : ℚ, Summable fun m : ℕ => ((w m : ℝ) : ℂ) * addChar ((m + 1 : ℕ) * x) :=
    fun x => Summable.of_norm_bounded (g := w) hws fun m => by
      rw [norm_mul, norm_addChar, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  -- exchange the finite sums with the series
  have hswap : ∑ j : Fin q, ∑ k : Fin q, bcSuccessor β ((((k : ℕ) : ℚ) - (j : ℕ)) / q) =
      (((bcPartition β)⁻¹ : ℝ) : ℂ) * ∑' m : ℕ, ((w m : ℝ) : ℂ) *
        (if q ∣ m + 1 then (q : ℂ) ^ 2 else 0) := by
    unfold bcSuccessor
    simp_rw [← Finset.mul_sum]
    congr 1
    have hinner : ∀ j : Fin q, ∑ k : Fin q, ∑' m : ℕ, ((w m : ℝ) : ℂ) *
        addChar ((m + 1 : ℕ) * ((((k : ℕ) : ℚ) - (j : ℕ)) / q)) =
        ∑' m : ℕ, ∑ k : Fin q, ((w m : ℝ) : ℂ) *
          addChar ((m + 1 : ℕ) * ((((k : ℕ) : ℚ) - (j : ℕ)) / q)) :=
      fun j => (Summable.tsum_finsetSum fun k _ => hsum _).symm
    simp only [hw] at hinner ⊢
    rw [Finset.sum_congr rfl fun j _ => hinner j]
    rw [← Summable.tsum_finsetSum fun j _ => summable_sum fun k _ => hsum _]
    refine tsum_congr fun m => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    have := sum_sum_addChar q hq (m + 1)
    push_cast at this ⊢
    exact this
  -- the series over multiples of `q`
  have hmult : ∑' m : ℕ, w m * (if q ∣ m + 1 then (1 : ℝ) else 0) = (q : ℝ) ^ (-β) * bcPartition β := by
    set f : ℕ → ℝ := fun m => w m * (if q ∣ m + 1 then (1 : ℝ) else 0) with hf
    set g : ℕ → ℕ := fun ℓ => q * (ℓ + 1) - 1 with hg
    have hginj : Function.Injective g := by
      intro a b hab
      simp only [hg] at hab
      have h1 : 1 ≤ q * (a + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have h2 : 1 ≤ q * (b + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have : q * (a + 1) = q * (b + 1) := by omega
      have := Nat.eq_of_mul_eq_mul_left hq this
      omega
    have hsupp : Function.support f ⊆ Set.range g := by
      intro m hm
      simp only [Function.mem_support, hf, ne_eq, mul_eq_zero, ite_eq_right_iff, one_ne_zero,
        imp_false, not_or, not_not] at hm
      obtain ⟨t, ht⟩ := hm.2
      have ht0 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · rw [h, mul_zero] at ht; omega
        · exact h
      refine ⟨t - 1, ?_⟩
      simp only [hg]
      rw [Nat.sub_add_cancel ht0, ← ht]
      omega
    rw [← hginj.tsum_eq hsupp]
    have hfg : ∀ ℓ : ℕ, f (g ℓ) = (q : ℝ) ^ (-β) * ((ℓ + 1 : ℕ) : ℝ) ^ (-β) := by
      intro ℓ
      have h1 : 1 ≤ q * (ℓ + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hdiv : q ∣ g ℓ + 1 := ⟨ℓ + 1, by simp only [hg]; omega⟩
      simp only [hf, hw, if_pos hdiv, mul_one]
      rw [show g ℓ + 1 = q * (ℓ + 1) by simp only [hg]; omega, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    simp_rw [hfg]
    rw [tsum_mul_left]
    rfl
  rw [hswap]
  have hcast : ∑' m : ℕ, ((w m : ℝ) : ℂ) * (if q ∣ m + 1 then (q : ℂ) ^ 2 else 0) =
      (((q : ℝ) ^ 2 * ((q : ℝ) ^ (-β) * bcPartition β) : ℝ) : ℂ) := by
    rw [← hmult, ← tsum_mul_left]
    push_cast
    refine tsum_congr fun m => ?_
    split_ifs <;> push_cast <;> ring
  rw [hcast]
  have hZC : (bcPartition β : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  push_cast
  field_simp

/-! ### Sharpness: the Bost–Connes ground state on `ℓ²(ℚ)` -/

/-- The ground-state amplitude `ξ_β(m) = (m^{−β}/Z_β)^{1/2}` on the positive integers. -/
def bcAmp (β : ℝ) (x : ℚ) : ℝ :=
  if x.den = 1 ∧ 0 < x then Real.sqrt ((x : ℝ) ^ (-β) / bcPartition β) else 0

/-- The value `1[α > 0]·(nd)^{−β/2}·ψ_β(dσ)` at slope `α = n/d` and shift `σ`. -/
def bcFormula (β : ℝ) (α σ : ℚ) : ℂ :=
  if 0 < α then ((((α.num.natAbs : ℝ) * α.den) ^ (-(β / 2)) : ℝ) : ℂ) * bcSuccessor β (α.den * σ)
  else 0

/-- The **Bost–Connes state** on `Aff(ℚ)`: `φ_β(x ↦ ax + b) = 1[a > 0]·(nd)^{−β/2}·ψ_β(db)`. -/
def bcState (β : ℝ) (g : AffineGroupQ) : ℂ := bcFormula β (affSlope g) (affShift g)

theorem bcAmp_ne_zero {β : ℝ} {x : ℚ} (h : bcAmp β x ≠ 0) : x.den = 1 ∧ 0 < x := by
  unfold bcAmp at h; split_ifs at h with hx; exact hx; exact absurd rfl h

theorem bcAmp_nat {β : ℝ} (m : ℕ) (hm : 0 < m) :
    bcAmp β m = Real.sqrt ((m : ℝ) ^ (-β) / bcPartition β) := by
  unfold bcAmp
  rw [if_pos ⟨Rat.den_natCast m, by exact_mod_cast hm⟩]
  push_cast; rfl

/-- The pair computation behind the ground state: the `ℓ²(ℚ)` inner product of the vectors of
`x ↦ ax + b` and `x ↦ a'x + b'` is summable and equals `bcFormula (a'/a) ((b' − b)/a)`. -/
theorem bcPair {β : ℝ} (hβ : 1 < β) {a a' : ℚ} (ha : a ≠ 0) (ha' : a' ≠ 0) (b b' : ℚ) :
    Summable (fun y : ℚ => star (addChar (b * y) * (bcAmp β (a * y) : ℂ)) *
        (addChar (b' * y) * (bcAmp β (a' * y) : ℂ))) ∧
      ∑' y : ℚ, star (addChar (b * y) * (bcAmp β (a * y) : ℂ)) *
        (addChar (b' * y) * (bcAmp β (a' * y) : ℂ)) = bcFormula β (a' / a) ((b' - b) / a) := by
  set f : ℚ → ℂ := fun y => star (addChar (b * y) * (bcAmp β (a * y) : ℂ)) *
    (addChar (b' * y) * (bcAmp β (a' * y) : ℂ)) with hf
  have hZ := bcPartition_pos hβ
  -- simplified form of the summand
  have hfe : ∀ y, f y = addChar ((b' - b) * y) * ((bcAmp β (a * y) * bcAmp β (a' * y) : ℝ) : ℂ) := by
    intro y
    simp only [hf, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.star_def, ← addChar_neg]
    rw [show (b' - b) * y = -(b * y) + b' * y by ring, addChar_add]
    push_cast; ring
  set α := a' / a with hα
  by_cases hpos : 0 < α
  · -- reindex the support along `ℓ ↦ d(ℓ+1)/a`
    set N := α.num.natAbs with hN
    set Dα := α.den with hDα
    have hDpos : 0 < Dα := α.den_pos
    have hNpos : 0 < N := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hpos.ne')
    set g : ℕ → ℚ := fun ℓ => ((Dα * (ℓ + 1) : ℕ) : ℚ) / a with hg
    have hginj : Function.Injective g := by
      intro x y hxy
      simp only [hg] at hxy
      have := (div_left_inj' ha).mp hxy
      have h2 : Dα * (x + 1) = Dα * (y + 1) := by exact_mod_cast this
      have := Nat.eq_of_mul_eq_mul_left hDpos h2
      omega
    have hnumα : (α.num : ℚ) = α * Dα := (Rat.mul_den_eq_num α).symm
    have hαN : (α.num : ℚ) = N := by
      rw [hN, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast Rat.num_pos.mpr hpos)]
    have hsupp : ∀ y ∉ Set.range g, f y = 0 := by
      intro y hy
      rw [hfe]
      by_contra hne
      have h1 : bcAmp β (a * y) ≠ 0 := fun h => hne (by rw [h, zero_mul]; push_cast; ring)
      have h2 : bcAmp β (a' * y) ≠ 0 := fun h => hne (by rw [h, mul_zero]; push_cast; ring)
      obtain ⟨hd1, hp1⟩ := bcAmp_ne_zero h1
      obtain ⟨hd2, hp2⟩ := bcAmp_ne_zero h2
      apply hy
      -- `a y = m` and `a' y = α m` are positive integers, so `d ∣ m`
      set m := (a * y).num with hm
      have hmy : ((m : ℤ) : ℚ) = a * y := (Rat.den_eq_one_iff _).mp hd1
      have hm0 : 0 < m := Rat.num_pos.mpr hp1
      have hαm : (a' * y) = α * m := by rw [hmy, hα]; field_simp
      have hint : ((α * m).den = 1) := by rw [← hαm]; exact hd2
      have hdvd : (Dα : ℤ) ∣ m := by
        have := (Rat.den_eq_one_iff _).mp hint
        -- `α m = N m / Dα` integral with `gcd(N, Dα) = 1`
        have hcop : Int.gcd α.num Dα = 1 := α.reduced
        have hq : (α * m : ℚ) = (α.num * m : ℤ) / Dα := by
          push_cast; rw [hnumα]; field_simp
        rw [hq] at hint
        have := (Rat.den_div_intCast_eq_one_iff _ _ (by exact_mod_cast hDpos.ne')).mp hint
        exact (Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_comm]; exact hcop)).dvd_of_dvd_mul_left this
      obtain ⟨t, ht⟩ := hdvd
      have ht0 : 0 < t := by
        rcases lt_trichotomy t 0 with h | h | h
        · nlinarith [hm0, show (0 : ℤ) < Dα by exact_mod_cast hDpos]
        · rw [h, mul_zero] at ht; omega
        · exact h
      refine ⟨t.toNat - 1, ?_⟩
      simp only [hg]
      have : ((t.toNat - 1 + 1 : ℕ) : ℤ) = t := by omega
      rw [div_eq_iff ha]
      have h2 : ((t.toNat - 1 : ℕ) : ℚ) + 1 = (t : ℚ) := by
        have h3 := congrArg (fun z : ℤ => (z : ℚ)) this
        push_cast at h3
        linarith
      have hcast : ((Dα * (t.toNat - 1 + 1) : ℕ) : ℚ) = (m : ℚ) := by
        rw [ht]; push_cast; rw [h2]
      rw [hcast, hmy]; ring
    -- the summand along the reindexing
    have hfg : ∀ ℓ : ℕ, f (g ℓ) = ((((N : ℝ) * Dα) ^ (-(β / 2)) : ℝ) : ℂ) *
        (((bcPartition β)⁻¹ : ℝ) * ((((ℓ + 1 : ℕ) : ℝ) ^ (-β) : ℝ) *
          addChar ((ℓ + 1 : ℕ) * (Dα * ((b' - b) / a))))) := by
      intro ℓ
      rw [hfe]
      have hay : a * g ℓ = ((Dα * (ℓ + 1) : ℕ) : ℚ) := by simp only [hg]; field_simp
      have ha'y : a' * g ℓ = ((N * (ℓ + 1) : ℕ) : ℚ) := by
        have h1 : a' * g ℓ = α * (Dα : ℚ) * ((ℓ : ℚ) + 1) := by
          simp only [hg, hα]; push_cast; field_simp
        have hαD : α * (Dα : ℚ) = (N : ℚ) := by rw [← hαN]; exact Rat.mul_den_eq_num α
        rw [h1, hαD]; push_cast; ring
      rw [hay, ha'y, bcAmp_nat _ (by positivity), bcAmp_nat _ (by positivity)]
      have hamp : Real.sqrt (((Dα * (ℓ + 1) : ℕ) : ℝ) ^ (-β) / bcPartition β) *
          Real.sqrt (((N * (ℓ + 1) : ℕ) : ℝ) ^ (-β) / bcPartition β) =
          ((N : ℝ) * Dα) ^ (-(β / 2)) * ((bcPartition β)⁻¹ * ((ℓ + 1 : ℕ) : ℝ) ^ (-β)) := by
        have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
        have hDR : (0 : ℝ) < Dα := by exact_mod_cast hDpos
        have hlR : (0 : ℝ) < ((ℓ + 1 : ℕ) : ℝ) := by positivity
        rw [← Real.sqrt_mul (by positivity)]
        have hY : (0 : ℝ) ≤ ((N : ℝ) * Dα) ^ (-(β / 2)) *
            ((bcPartition β)⁻¹ * ((ℓ + 1 : ℕ) : ℝ) ^ (-β)) := by positivity
        rw [← Real.sqrt_sq hY]
        congr 1
        have e1 : (N : ℝ) ^ (-(β / 2)) * (N : ℝ) ^ (-(β / 2)) = (N : ℝ) ^ (-β) := by
          rw [← Real.rpow_add hNR]; ring_nf
        have e2 : (Dα : ℝ) ^ (-(β / 2)) * (Dα : ℝ) ^ (-(β / 2)) = (Dα : ℝ) ^ (-β) := by
          rw [← Real.rpow_add hDR]; ring_nf
        rw [Nat.cast_mul, Nat.cast_mul, Real.mul_rpow hDR.le hlR.le, Real.mul_rpow hNR.le hlR.le,
          Real.mul_rpow hNR.le hDR.le]
        rw [show ((N : ℝ) ^ (-(β / 2)) * (Dα : ℝ) ^ (-(β / 2)) *
            ((bcPartition β)⁻¹ * ((ℓ + 1 : ℕ) : ℝ) ^ (-β))) ^ 2 =
            ((N : ℝ) ^ (-(β / 2)) * (N : ℝ) ^ (-(β / 2))) *
            ((Dα : ℝ) ^ (-(β / 2)) * (Dα : ℝ) ^ (-(β / 2))) *
            ((bcPartition β)⁻¹ * ((ℓ + 1 : ℕ) : ℝ) ^ (-β)) ^ 2 by ring, e1, e2]
        field_simp
      rw [hamp]
      rw [show (b' - b) * g ℓ = ((ℓ + 1 : ℕ) : ℚ) * (Dα * ((b' - b) / a)) by
        simp only [hg]; push_cast; field_simp]
      push_cast; ring
    have hsumg : Summable (f ∘ g) := by
      have hb := (summable_bcWeight hβ)
      refine Summable.of_norm_bounded (g := fun ℓ => ((N : ℝ) * Dα) ^ (-(β / 2)) *
        ((bcPartition β)⁻¹ * ((ℓ + 1 : ℕ) : ℝ) ^ (-β))) ((hb.mul_left _).mul_left _) fun ℓ => ?_
      simp only [Function.comp_apply, hfg, norm_mul, norm_addChar, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) * Dα) _),
        Real.norm_of_nonneg (inv_nonneg.mpr hZ.le),
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), mul_one]
      exact le_refl _
    have hsum : Summable f := (hginj.summable_iff hsupp).mp hsumg
    refine ⟨hsum, ?_⟩
    rw [← hginj.tsum_eq (fun y hy => by_contra fun hny => hy (hsupp y hny))]
    simp_rw [hfg]
    rw [tsum_mul_left, tsum_mul_left]
    unfold bcFormula bcSuccessor
    rw [if_pos hpos]
  · -- no common support when the slopes have opposite signs
    have hzero : ∀ y, f y = 0 := by
      intro y
      rw [hfe]
      by_contra hne
      have h1 : bcAmp β (a * y) ≠ 0 := fun h => hne (by rw [h, zero_mul]; push_cast; ring)
      have h2 : bcAmp β (a' * y) ≠ 0 := fun h => hne (by rw [h, mul_zero]; push_cast; ring)
      obtain ⟨-, hp1⟩ := bcAmp_ne_zero h1
      obtain ⟨-, hp2⟩ := bcAmp_ne_zero h2
      apply hpos
      rw [hα, show a' / a = (a' * y) / (a * y) by
        have hy : y ≠ 0 := by rintro rfl; simp at hp1
        field_simp]
      exact div_pos hp2 hp1
    have hf0 : f = fun _ => 0 := funext hzero
    refine ⟨by rw [hf0]; exact summable_zero, ?_⟩
    rw [hf0, tsum_zero]
    unfold bcFormula
    rw [if_neg hpos]

/-- **The Bost–Connes state is positive definite**: it is the coefficient
`⟨π(g)ξ_β, ξ_β⟩` of the ground state `ξ_β` in `ℓ²(ℚ)`, where `π(x ↦ ax + b)v(y) = e(by)v(ay)`. -/
theorem isPosDefOnGroup_bcState {β : ℝ} (hβ : 1 < β) : IsPosDefOnGroup (bcState β) := by
  intro N x c
  set v : Fin N → ℚ → ℂ := fun i y =>
    addChar (affShift (x i) * y) * (bcAmp β (affSlope (x i) * y) : ℂ) with hv
  have hpair : ∀ i j, Summable (fun y => star (v i y) * v j y) ∧
      ∑' y, star (v i y) * v j y = bcState β ((x i)⁻¹ * x j) := by
    intro i j
    obtain ⟨h1, h2⟩ := bcPair hβ (affSlope_ne_zero (x i)) (affSlope_ne_zero (x j))
      (affShift (x i)) (affShift (x j))
    refine ⟨h1, ?_⟩
    rw [h2, bcState, affSlope_mul, affSlope_inv, affShift_mul, affShift_inv, affSlope_inv]
    have hi := affSlope_ne_zero (x i)
    congr 1
    · field_simp
    · field_simp; ring
  refine ⟨∑' y, Complex.normSq (∑ j, c j * v j y),
    tsum_nonneg fun y => Complex.normSq_nonneg _, ?_⟩
  have hterm : ∀ y, ((Complex.normSq (∑ j, c j * v j y) : ℝ) : ℂ) =
      ∑ i, ∑ j, star (c i) * (star (v i y) * v j y) * c j := by
    intro y
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']; ring
  rw [Complex.ofReal_tsum]
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ =>
    ((hpair i j).1.mul_left _).mul_right _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum fun j _ => ((hpair i j).1.mul_left _).mul_right _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_right, tsum_mul_left, (hpair i j).2]

theorem bcSuccessor_int {β : ℝ} (hβ : 1 < β) (m : ℤ) : bcSuccessor β m = 1 := by
  have hZ := bcPartition_pos hβ
  unfold bcSuccessor
  have h : ∀ k : ℕ, addChar ((k + 1 : ℕ) * (m : ℚ)) = 1 := fun k => by
    rw [show ((k + 1 : ℕ) : ℚ) * (m : ℚ) = (((k + 1 : ℕ) * m : ℤ) : ℚ) by push_cast; ring]
    exact addChar_int _
  simp_rw [h, mul_one]
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_mul]
  have e : ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-β) = bcPartition β := rfl
  rw [e, inv_mul_cancel₀ hZ.ne', Complex.ofReal_one]

/-- The Bost–Connes state has successor `ψ_β`. -/
theorem bcState_translation (β : ℝ) (b : ℚ) : bcState β (translation b) = bcSuccessor β b := by
  simp [bcState, bcFormula, affSlope_translation, affShift_translation]

/-- On the dilations the Bost–Connes state is `(nd)^{−β/2}`. -/
theorem bcState_dilation {β : ℝ} (hβ : 1 < β) (u : ℚˣ) (hu : 0 < (u : ℚ)) :
    bcState β (dilation u) = (((((u : ℚ).num.natAbs : ℝ) * (u : ℚ).den) ^ (-(β / 2)) : ℝ) : ℂ) := by
  simp only [bcState, bcFormula, affSlope_dilation, affShift_dilation, mul_zero, if_pos hu]
  rw [show ((0 : ℚ)) = ((0 : ℤ) : ℚ) by simp, bcSuccessor_int hβ, mul_one]

/-- **The Bost–Connes temperature is the Hecke exponent.** For `β > 1`, every positive-definite
`φ` on `Aff(ℚ)` with successor `ψ_β` satisfies `|φ(x ↦ ux)|² ≤ (nd)^{−β}` at `u = ±n/d`, and the
Bost–Connes state attains equality at every positive `u`. -/
theorem bc_successor_hecke_exponent {β : ℝ} (hβ : 1 < β) :
    (∀ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ → (∀ b, φ (translation b) = bcSuccessor β b) →
      ∀ u : ℚˣ, Complex.normSq (φ (dilation u)) ≤
        (((u : ℚ).num.natAbs : ℝ) * (u : ℚ).den) ^ (-β)) ∧
    IsPosDefOnGroup (bcState β) ∧ (∀ b, bcState β (translation b) = bcSuccessor β b) ∧
    ∀ u : ℚˣ, 0 < (u : ℚ) → Complex.normSq (bcState β (dilation u)) =
      (((u : ℚ).num.natAbs : ℝ) * (u : ℚ).den) ^ (-β) := by
  refine ⟨fun φ hφ hs u => ?_, isPosDefOnGroup_bcState hβ, bcState_translation β, fun u hu => ?_⟩
  · have h1 : φ 1 = 1 := by
      rw [← translation_zero, hs, show (0 : ℚ) = ((0 : ℤ) : ℚ) by simp, bcSuccessor_int hβ]
    have hper : ∀ m : ℤ, φ (translation m) = φ 1 := fun m => by rw [hs, bcSuccessor_int hβ, h1]
    have hlaw := normSq_dilation_le_successorDensity hφ hper u
    have hdens : ∀ q : ℕ, 0 < q → successorDensity φ q = (((q : ℝ) ^ (-β) : ℝ) : ℂ) := by
      intro q hq
      unfold successorDensity
      simp_rw [hs]
      exact bcDensity hβ q hq
    rw [hdens _ (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)), hdens _ (u : ℚ).den_pos,
      Complex.ofReal_re, Complex.ofReal_re] at hlaw
    rwa [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  · rw [bcState_dilation hβ u hu, Complex.normSq_ofReal, ← Real.rpow_add' (by positivity)
      (by intro h; linarith)]
    ring_nf

end GaloisForLFunctions.ArithmeticPositiveDuality
