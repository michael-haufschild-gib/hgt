import GaloisForLFunctions.RHTower.HalfWeightEisensteinCoefficients

/-!
# Theta series twisted by a Dirichlet character

For odd `q` and a Dirichlet character `ψ` mod `q`:

* `gaussQ_add_quot`: `G(m + (c/q)k; c) = G(m; c)` for `c = q²f` and `(m,q) = 1`. The shifts
  `r ↦ r + (c/q)t` multiply `e((m+(c/q)k) r²/c)` by `e(2mrt/q)`, so averaging over `t` localises
  both sums to `q ∣ r`, where the two summands agree.
* **`theta_translate`**: for `γ ∈ Γ₀(4q²)`, `θ(γz + a/q) = J(γ,z) θ(z + ad²/q)`. The matrix
  `[[1,a/q],[0,1]] γ [[1,-ad²/q],[0,1]]` is integral with bottom row `(c, d - (c/q)ad²)`, and its theta
  multiplier equals `J(γ,z)` by `J_mul_gauss` and `gaussQ_add_quot`.
* `thetaTw`: `θ_ψ(z) = Σ_{a mod q} ψ̄(a) θ(z + a/q)`, and **`thetaTw_smul`**:
  `θ_ψ(γz) = ψ(d)² J(γ,z) θ_ψ(z)` on `Γ₀(4q²)` (reindex `a ↦ ad²`).
* `thetaTw_hasSum`: `θ_ψ(v) = Σ_n g_ψ(n²) e(n²v)` with `g_ψ(n) = Σ_a ψ̄(a) e(an/q)`.

These are the kernels of Shimura's integral for `L(s, sym² u ⊗ ψ²)`.
-/

open Complex Matrix Filter Topology
open scoped MatrixGroups Real

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.CoprimeClassExact GaloisForLFunctions.RHTower.CoprimeClassRamanujan

/-! ### Sums of periodic functions over a full period -/

theorem periodic_emod {c : ℕ} {F : ℤ → ℂ} (hF : Function.Periodic F (c : ℤ)) (r : ℤ) :
    F (r % c) = F r := by
  rw [Int.emod_def, show (c : ℤ) * (r / c) = (r / c) * c from mul_comm _ _]
  exact hF.sub_int_mul_eq _

theorem toNat_emod_modEq {c : ℕ} (hc : 0 < c) {r : ℕ} (hr : r < c) {a : ℤ}
    (ha : a ≡ r [ZMOD c]) : (a % c).toNat = r := by
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  rw [ha.eq, Int.emod_eq_of_lt (by positivity) (by omega)]
  simp

theorem sum_range_shift {c : ℕ} (hc : 0 < c) {F : ℤ → ℂ} (hF : Function.Periodic F (c : ℤ))
    (s : ℤ) : ∑ r ∈ Finset.range c, F ((r : ℤ) + s) = ∑ r ∈ Finset.range c, F r := by
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  refine Finset.sum_nbij' (fun r => (((r : ℤ) + s) % c).toNat) (fun r => (((r : ℤ) - s) % c).toNat)
    ?_ ?_ ?_ ?_ ?_
  · intro r _
    rw [Finset.mem_range]
    have h0 := Int.emod_nonneg ((r : ℤ) + s) hc'.ne'
    have h1 := Int.emod_lt_of_pos ((r : ℤ) + s) hc'
    omega
  · intro r _
    rw [Finset.mem_range]
    have h0 := Int.emod_nonneg ((r : ℤ) - s) hc'.ne'
    have h1 := Int.emod_lt_of_pos ((r : ℤ) - s) hc'
    omega
  · intro r hr
    rw [Finset.mem_range] at hr
    have h0 := Int.emod_nonneg ((r : ℤ) + s) hc'.ne'
    rw [Int.toNat_of_nonneg h0]
    refine toNat_emod_modEq hc hr ?_
    have := (Int.mod_modEq ((r : ℤ) + s) c).sub_right s
    simpa using this
  · intro r hr
    rw [Finset.mem_range] at hr
    have h0 := Int.emod_nonneg ((r : ℤ) - s) hc'.ne'
    rw [Int.toNat_of_nonneg h0]
    refine toNat_emod_modEq hc hr ?_
    have := (Int.mod_modEq ((r : ℤ) - s) c).add_right s
    simpa using this
  · intro r _
    have h0 := Int.emod_nonneg ((r : ℤ) + s) hc'.ne'
    rw [Int.toNat_of_nonneg h0, periodic_emod hF]

/-! ### A shift invariance of quadratic Gauss sums -/

/-- The summand `r ↦ e(a r²/c)` of `G(a; c)`. -/
noncomputable def gq (a : ℤ) (c : ℕ) (r : ℤ) : ℂ := cexp (2 * π * I * (a * (r : ℂ) ^ 2 / c))

theorem gaussQ_eq_sum_range (a : ℤ) (c : ℕ) :
    gaussQ a c = ∑ r ∈ Finset.range c, gq a c r := by
  unfold gaussQ gq
  rw [Fin.sum_univ_eq_sum_range (fun r => cexp (2 * π * I * (a * ((r : ℕ) : ℂ) ^ 2 / c)))]
  simp

theorem gq_periodic (a : ℤ) {c : ℕ} (hc : c ≠ 0) : Function.Periodic (gq a c) (c : ℤ) := by
  intro r
  unfold gq
  have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  rw [show 2 * π * I * (a * (((r + c : ℤ)) : ℂ) ^ 2 / c) =
      2 * π * I * (a * (r : ℂ) ^ 2 / c) + ((a * (2 * r + c) : ℤ) : ℂ) * (2 * π * I) by
    push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem gq_shift (m k : ℤ) {q f : ℕ} (hq : q ≠ 0) (hf : f ≠ 0) (r : ℤ) (t : ℕ) :
    gq (m + (q * f : ℕ) * k) (q * (q * f)) (r + ((q * f : ℕ) : ℤ) * t) =
      gq (m + (q * f : ℕ) * k) (q * (q * f)) r * ph (2 * m * r) q t := by
  unfold gq ph
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hfC : (f : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hf
  rw [← Complex.exp_add]
  rw [show 2 * π * I * (((m + ((q * f : ℕ) : ℤ) * k : ℤ) : ℂ) * (((r + ((q * f : ℕ) : ℤ) * t : ℤ)) : ℂ) ^ 2 /
      ((q * (q * f) : ℕ) : ℂ)) = 2 * π * I * (((m + ((q * f : ℕ) : ℤ) * k : ℤ) : ℂ) * (r : ℂ) ^ 2 /
      ((q * (q * f) : ℕ) : ℂ)) + 2 * π * I * ((2 * m * r : ℤ) : ℂ) * ((t : ℕ) : ℂ) / q +
      ((2 * f * k * r * t + (m + q * f * k) * f * t ^ 2 : ℤ) : ℂ) * (2 * π * I) by
    push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem dvd_two_mul_iff {q : ℕ} (hq : Odd q) {m : ℤ} (hm : IsCoprime m q) (r : ℤ) :
    (q : ℤ) ∣ 2 * m * r ↔ (q : ℤ) ∣ r := by
  have h2 : IsCoprime (2 : ℤ) q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 2 q := (Nat.coprime_two_left).2 hq
    simpa [Int.gcd] using this
  have h2m : IsCoprime (q : ℤ) (2 * m) := (h2.mul_left hm).symm
  exact ⟨fun h => h2m.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h _⟩

/-- Averaging over the shifts `r ↦ r + (c/q) t` localises `G(m + (c/q)k; c)` to `q ∣ r`. -/
theorem gaussQ_eq_filter {q f : ℕ} (hq : Odd q) (hf : f ≠ 0) {m : ℤ} (hm : IsCoprime m q) (k : ℤ) :
    gaussQ (m + (q * f : ℕ) * k) (q * (q * f)) = ∑ r ∈ Finset.range (q * (q * f)),
      if (q : ℤ) ∣ r then gq (m + (q * f : ℕ) * k) (q * (q * f)) r else 0 := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have hc : 0 < q * (q * f) := by positivity
  have hP := gq_periodic (m + ((q * f : ℕ) : ℤ) * k) hc.ne'
  rw [gaussQ_eq_sum_range]
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have havg : ∑ r ∈ Finset.range (q * (q * f)), gq (m + ((q * f : ℕ) : ℤ) * k) (q * (q * f)) r =
      (1 / q) * ∑ t ∈ Finset.range q, ∑ r ∈ Finset.range (q * (q * f)),
        gq (m + ((q * f : ℕ) : ℤ) * k) (q * (q * f)) ((r : ℤ) + ((q * f : ℕ) : ℤ) * t) := by
    simp_rw [sum_range_shift hc hP]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [havg]
  simp_rw [gq_shift m k hq0 hf]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum, geom_eq hqpos]
  simp only [dvd_two_mul_iff hq hm]
  split_ifs
  · field_simp
  · simp

theorem gq_add_of_dvd {q f : ℕ} (hq : q ≠ 0) (hf : f ≠ 0) (m k : ℤ) {r : ℤ} (hr : (q : ℤ) ∣ r) :
    gq (m + (q * f : ℕ) * k) (q * (q * f)) r = gq m (q * (q * f)) r := by
  obtain ⟨s, rfl⟩ := hr
  unfold gq
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hfC : (f : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hf
  rw [show 2 * π * I * (((m + ((q * f : ℕ) : ℤ) * k : ℤ) : ℂ) * (((q * s : ℤ)) : ℂ) ^ 2 /
      ((q * (q * f) : ℕ) : ℂ)) = 2 * π * I * ((m : ℂ) * (((q * s : ℤ)) : ℂ) ^ 2 /
      ((q * (q * f) : ℕ) : ℂ)) + (((q : ℤ) * k * s ^ 2 : ℤ) : ℂ) * (2 * π * I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Invariance of the quadratic Gauss sum**: for odd `q`, `(m, q) = 1` and `c = q²f`,
`G(m + (c/q) k; c) = G(m; c)`. -/
theorem gaussQ_add_quot {q f : ℕ} (hq : Odd q) (hf : f ≠ 0) {m : ℤ} (hm : IsCoprime m q) (k : ℤ) :
    gaussQ (m + (q * f : ℕ) * k) (q * (q * f)) = gaussQ m (q * (q * f)) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have h0 := gaussQ_eq_filter hq hf hm 0
  simp only [mul_zero, add_zero] at h0
  rw [gaussQ_eq_filter hq hf hm k, h0]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with hr
  · exact gq_add_of_dvd hq0 hf m k hr
  · rfl

/-! ### Theta translated by `a/q` under `Γ₀(4q²)` -/

theorem gamma0_four_of_dvd {γ : SL(2, ℤ)} {c : ℕ} (hc : ent γ 1 0 = c) (h4 : 4 ∣ c) :
    γ ∈ CongruenceSubgroup.Gamma0 4 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  have : (4 : ℤ) ∣ ent γ 1 0 := by rw [hc]; exact_mod_cast h4
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 this

theorem isCoprime_d_of_dvd {γ : SL(2, ℤ)} {q : ℕ} (hq : (q : ℤ) ∣ ent γ 1 0) :
    IsCoprime (ent γ 1 1) q := by
  obtain ⟨t, ht⟩ := hq
  have hdet := det_entries γ
  exact ⟨ent γ 0 0, -(ent γ 0 1 * t), by rw [ht] at hdet; linear_combination hdet⟩

/-- The positive case of `theta_translate`. -/
theorem theta_translate_pos {q F : ℕ} (hq : Odd q) (hF : F ≠ 0) (h4F : 4 ∣ F) {γ : SL(2, ℤ)}
    (hc : ent γ 1 0 = ((q * (q * F) : ℕ) : ℤ)) (a : ℤ) (z : UpperHalfPlane) :
    theta ((γ • z : UpperHalfPlane) + (a : ℂ) / q) =
      J γ z * theta ((z : ℂ) + a * (ent γ 1 1 : ℂ) ^ 2 / q) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq0
  obtain ⟨α, hα⟩ : ∃ α, ent γ 0 0 = α := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, ent γ 0 1 = β := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, ent γ 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, ent γ 1 1 = d := ⟨_, rfl⟩
  have hdet : α * d - β * c = 1 := by rw [← hα, ← hβ, ← hc', ← hd]; exact det_entries γ
  have hcq : c = q * q * F := by rw [← hc', hc]; push_cast; ring
  let γ' : SL(2, ℤ) := ⟨!![α + a * q * F, β - a * d * β * q * F - a ^ 2 * d ^ 2 * F;
      c, d - q * F * a * d ^ 2], by
    rw [Matrix.det_fin_two_of]
    linear_combination (1 - a * q * F * d) * hdet + a ^ 2 * d ^ 2 * F * hcq⟩
  have e10 : ent γ' 1 0 = c := by simp [ent, γ']
  have e11 : ent γ' 1 1 = d - q * F * a * d ^ 2 := by simp [ent, γ']
  have e00 : ent γ' 0 0 = α + a * q * F := by simp [ent, γ']
  have e01 : ent γ' 0 1 = β - a * d * β * q * F - a ^ 2 * d ^ 2 * F := by simp [ent, γ']
  set w : UpperHalfPlane := ((a * d ^ 2 / q : ℝ)) +ᵥ z with hw
  have hwC : (w : ℂ) = (z : ℂ) + a * (d : ℂ) ^ 2 / q := by
    rw [hw, UpperHalfPlane.coe_vadd]; push_cast; ring
  have hcz : (c : ℂ) * z + d ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ z
    rwa [denom_ent, hc', hd] at this
  have hcqC : (c : ℂ) = q * q * F := by exact_mod_cast hcq
  have hcw : (c : ℂ) * w + ((d - q * F * a * d ^ 2 : ℤ) : ℂ) = (c : ℂ) * z + d := by
    rw [hwC, hcqC]; push_cast; field_simp; ring
  have hact : ((γ' • w : UpperHalfPlane) : ℂ) = (γ • z : UpperHalfPlane) + (a : ℂ) / q := by
    rw [coe_smul_ent, coe_smul_ent, e00, e01, e10, e11, hcw, hα, hβ, hc', hd,
      div_add_div _ _ hcz hqC, div_eq_div_iff hcz (mul_ne_zero hcz hqC)]
    have hdetC : (α : ℂ) * d - β * c = 1 := by exact_mod_cast hdet
    have hwq : (w : ℂ) * q = z * q + a * d ^ 2 := by rw [hwC]; field_simp
    push_cast
    linear_combination ((a : ℂ) * d * ((c : ℂ) * z + d)) * hdetC +
      (-(a : ℂ) * ((z : ℂ) - d * β) * ((c : ℂ) * z + d)) * hcqC +
      (((α : ℂ) + a * q * F) * ((c : ℂ) * z + d)) * hwq
  haveI : NeZero (q * (q * F)) := ⟨by positivity⟩
  have h4c : 4 ∣ q * (q * F) := dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h4F _) _
  have hγ4 := gamma0_four_of_dvd hc h4c
  have hγ'4 : γ' ∈ CongruenceSubgroup.Gamma0 4 :=
    gamma0_four_of_dvd (by rw [e10, ← hc', hc]) h4c
  have hJ := J_mul_gauss hγ4 hc z
  have hJ' := J_mul_gauss hγ'4 (by rw [e10, ← hc', hc]) w
  have hdq : IsCoprime (-d) (q : ℤ) := by
    have := isCoprime_d_of_dvd (γ := γ) (q := q) (by rw [hc]; push_cast; exact dvd_mul_right _ _)
    rw [hd] at this
    exact this.neg_left
  have hg : gaussQ (-ent γ' 1 1) (q * (q * F)) = gaussQ (-d) (q * (q * F)) := by
    rw [e11, show -(d - q * F * a * d ^ 2) = -d + ((q * F : ℕ) : ℤ) * (a * d ^ 2) by push_cast; ring]
    exact gaussQ_add_quot hq hF hdq _
  rw [hg, e11] at hJ'
  have hcC : ((q * (q * F) : ℕ) : ℂ) = (c : ℂ) := by rw [hcqC]; push_cast; ring
  rw [hcC, hcw] at hJ'
  rw [hcC, hd] at hJ
  have hK : gaussQ (-d) (q * (q * F)) * (I * (c : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h0
      have hcop : IsCoprime ((q * (q * F) : ℕ) : ℤ) d := by
        rw [← hc, ← hd]; exact isCoprime_cd γ
      have := norm_sq_gaussQ (c := q * (q * F)) (by exact_mod_cast h4c) hcop
      rw [h0, norm_zero] at this
      have : (0 : ℝ) < 2 * ((q * (q * F) : ℕ) : ℝ) := by positivity
      linarith
    · rw [Ne, Complex.cpow_eq_zero_iff]
      push Not
      intro h0
      rw [hcqC] at h0
      simp at h0
      tauto
  have hJJ : J γ' w = J γ z := mul_right_cancel₀ hK (hJ'.trans hJ.symm)
  rw [← hact, theta_smul, hJJ, hwC, hd]

/-- **Theta translated by `a/q`**: for odd `q` and `γ ∈ Γ₀(4q²)`,
`θ(γz + a/q) = J(γ,z) θ(z + a d²/q)`. The matrix `[[1, a/q],[0,1]] γ [[1, -ad²/q],[0,1]]` is integral
with the same bottom row modulo `c/q`, and the quadratic Gauss sum is invariant under that change
(`gaussQ_add_quot`). -/
theorem theta_translate {q : ℕ} (hq : Odd q) {γ : SL(2, ℤ)} (hγ : ((4 * q ^ 2 : ℕ) : ℤ) ∣ ent γ 1 0)
    (a : ℤ) (z : UpperHalfPlane) :
    theta ((γ • z : UpperHalfPlane) + (a : ℂ) / q) =
      J γ z * theta ((z : ℂ) + a * (ent γ 1 1 : ℂ) ^ 2 / q) := by
  obtain ⟨t, ht⟩ := hγ
  rcases lt_trichotomy t 0 with h | h | h
  · have hn : ent (-γ) 1 0 = ((q * (q * (4 * (-t).toNat)) : ℕ) : ℤ) := by
      rw [ent_neg, ht]; push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring
    have := theta_translate_pos hq (by omega) (dvd_mul_right 4 _) hn a z
    rwa [ModularGroup.SL_neg_smul, J_neg, ent_neg, Int.cast_neg, neg_sq] at this
  · subst h
    have hc : ent γ 1 0 = 0 := by rw [ht]; ring
    have hdet := det_entries γ
    rw [hc, mul_zero, sub_zero] at hdet
    rw [J_of_c_zero γ hc, one_mul, coe_smul_ent, hc]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · rw [ha, hd]
      have : ((1 : ℤ) * (z : ℂ) + ent γ 0 1) / (((0 : ℤ) : ℂ) * z + ((1 : ℤ) : ℂ)) + (a : ℂ) / q =
          ((z : ℂ) + (a : ℂ) * ((1 : ℤ) : ℂ) ^ 2 / q) + (ent γ 0 1 : ℤ) := by push_cast; ring
      rw [this, theta_add_int]
    · rw [ha, hd]
      have : (((-1 : ℤ) : ℂ) * (z : ℂ) + ent γ 0 1) / (((0 : ℤ) : ℂ) * z + ((-1 : ℤ) : ℂ)) +
          (a : ℂ) / q = ((z : ℂ) + (a : ℂ) * ((-1 : ℤ) : ℂ) ^ 2 / q) + ((-ent γ 0 1 : ℤ) : ℂ) := by
        push_cast; field_simp; ring
      rw [this, theta_add_int]
  · have hn : ent γ 1 0 = ((q * (q * (4 * t.toNat)) : ℕ) : ℤ) := by
      rw [ht]; push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring
    exact theta_translate_pos hq (by omega) (dvd_mul_right 4 _) hn a z

/-! ### The twisted theta series -/

section Twisted

variable {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)

/-- `θ_ψ(z) = Σ_{a mod q} ψ̄(a) θ(z + a/q)`, whose `n²`-th coefficient is `Σ_a ψ̄(a) e(an²/q)`. -/
noncomputable def thetaTw (z : ℂ) : ℂ :=
  ∑ a : ZMod q, starRingEnd ℂ (ψ a) * theta (z + ((a.val : ℕ) : ℂ) / q)

theorem theta_add_val (w : ℂ) (x : ℤ) :
    theta (w + ((((x : ZMod q)).val : ℕ) : ℂ) / q) = theta (w + (x : ℂ) / q) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have hv : ((((x : ZMod q)).val : ℕ) : ℤ) = x - q * (x / q) := by
    rw [ZMod.val_intCast, Int.emod_def]
  have : w + ((((x : ZMod q)).val : ℕ) : ℂ) / q = (w + (x : ℂ) / q) + ((-(x / q) : ℤ) : ℂ) := by
    have hv' : ((((x : ZMod q)).val : ℕ) : ℂ) = (x : ℂ) - q * ((x / q : ℤ) : ℂ) := by
      exact_mod_cast hv
    rw [hv']; push_cast; field_simp; ring
  rw [this, theta_add_int]

variable {ψ}

omit [NeZero q] in
theorem conj_char_units_inv (u : (ZMod q)ˣ) :
    starRingEnd ℂ (ψ ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) = ψ u := by
  have h1 : ψ u * ψ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hn := DirichletCharacter.unit_norm_eq_one ψ u
  have hinv : ψ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = starRingEnd ℂ (ψ u) := by
    have hz : ψ (u : ZMod q) ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    have hc : ψ (u : ZMod q) * starRingEnd ℂ (ψ u) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    exact mul_left_cancel₀ hz (h1.trans hc.symm)
  rw [hinv, Complex.conj_conj]

/-- **The transformation law of `θ_ψ`**: for odd `q` and `γ ∈ Γ₀(4q²)`,
`θ_ψ(γz) = ψ(d)² J(γ,z) θ_ψ(z)`. -/
theorem thetaTw_smul (hq : Odd q) {γ : SL(2, ℤ)} (hγ : ((4 * q ^ 2 : ℕ) : ℤ) ∣ ent γ 1 0)
    (z : UpperHalfPlane) :
    thetaTw ψ ((γ • z : UpperHalfPlane) : ℂ) =
      ψ ((ent γ 1 1 : ℤ) : ZMod q) ^ 2 * J γ z * thetaTw ψ z := by
  have hqd : (q : ℤ) ∣ ent γ 1 0 := by
    refine dvd_trans ?_ hγ
    push_cast
    exact ⟨4 * q, by ring⟩
  have hdu : IsUnit ((ent γ 1 1 : ℤ) : ZMod q) := by
    obtain ⟨u', v', huv⟩ := isCoprime_d_of_dvd hqd
    have h1 : ((ent γ 1 1 : ℤ) : ZMod q) * ((u' : ℤ) : ZMod q) = 1 := by
      have := congrArg (fun t : ℤ => (t : ZMod q)) huv
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, add_zero] at this
      rw [mul_comm]; exact this
    exact IsUnit.of_mul_eq_one _ h1
  obtain ⟨u, hu⟩ := hdu
  unfold thetaTw
  have step : ∀ a : ZMod q, starRingEnd ℂ (ψ a) *
      theta (((γ • z : UpperHalfPlane) : ℂ) + ((a.val : ℕ) : ℂ) / q) =
      J γ z * (starRingEnd ℂ (ψ a) * theta ((z : ℂ) + (((a * (u : ZMod q) ^ 2).val : ℕ) : ℂ) / q)) := by
    intro a
    have h := theta_translate hq hγ (a.val : ℤ) z
    push_cast at h
    rw [h]
    have hx : ((((a.val : ℤ) * ent γ 1 1 ^ 2 : ℤ) : ZMod q)) = a * (u : ZMod q) ^ 2 := by
      push_cast; rw [hu]; simp
    have := theta_add_val (q := q) (z : ℂ) ((a.val : ℤ) * ent γ 1 1 ^ 2)
    rw [hx] at this
    rw [this]; push_cast; ring
  simp_rw [step]
  rw [← Finset.mul_sum]
  have hre : ∑ a : ZMod q, starRingEnd ℂ (ψ a) *
      theta ((z : ℂ) + (((a * (u : ZMod q) ^ 2).val : ℕ) : ℂ) / q) =
      ψ (u : ZMod q) ^ 2 * ∑ b : ZMod q, starRingEnd ℂ (ψ b) * theta ((z : ℂ) + ((b.val : ℕ) : ℂ) / q) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Units.mulRight (u ^ 2)) _ _ fun a => ?_
    simp only [Units.mulRight_apply, Units.val_pow_eq_pow_val]
    have : a = (a * (u : ZMod q) ^ 2) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) ^ 2 := by
      rw [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
    have hψ : starRingEnd ℂ (ψ a) = starRingEnd ℂ (ψ (a * (u : ZMod q) ^ 2)) * ψ (u : ZMod q) ^ 2 := by
      conv_lhs => rw [this]
      rw [map_mul, map_pow, map_mul, map_pow, conj_char_units_inv]
    rw [hψ]
    ring
  rw [hre, hu]
  ring

variable (ψ)

theorem differentiableAt_thetaTw {v : ℂ} (hv : 0 < v.im) : DifferentiableAt ℂ (thetaTw ψ) v := by
  unfold thetaTw
  refine DifferentiableAt.fun_sum fun a _ => ?_
  refine (differentiableAt_const _).mul ?_
  have h : 0 < (v + ((a.val : ℕ) : ℂ) / q).im := by
    have : (((a.val : ℕ) : ℂ) / q).im = 0 := by
      rw [show ((a.val : ℕ) : ℂ) / q = (((a.val : ℝ) / q : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_im _
    rw [Complex.add_im, this, add_zero]; exact hv
  have hc := (differentiableAt_theta h).comp (𝕜 := ℂ) v
    ((differentiableAt_id (x := v)).add_const (((a.val : ℕ) : ℂ) / q))
  exact hc

/-- The coefficient `g_ψ(n) = Σ_{a mod q} ψ̄(a) e(an/q)` of `θ_ψ` at `n`. -/
noncomputable def gTw (n : ℤ) : ℂ :=
  ∑ a : ZMod q, starRingEnd ℂ (ψ a) * cexp (2 * π * I * ((a.val : ℕ) : ℂ) * n / q)

/-- **The Fourier expansion of `θ_ψ`**: `θ_ψ(v) = Σ_n g_ψ(n²) e(n² v)`. -/
theorem thetaTw_hasSum {v : ℂ} (hv : 0 < v.im) :
    HasSum (fun n : ℤ => gTw ψ (n ^ 2) * cexp (2 * π * I * (n : ℂ) ^ 2 * v)) (thetaTw ψ v) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  have hterm : ∀ a : ZMod q, HasSum (fun n : ℤ => starRingEnd ℂ (ψ a) *
      cexp (2 * π * I * (n : ℂ) ^ 2 * (v + ((a.val : ℕ) : ℂ) / q)))
      (starRingEnd ℂ (ψ a) * theta (v + ((a.val : ℕ) : ℂ) / q)) := by
    intro a
    have h : 0 < (v + ((a.val : ℕ) : ℂ) / q).im := by
      have : (((a.val : ℕ) : ℂ) / q).im = 0 := by
        rw [show ((a.val : ℕ) : ℂ) / q = (((a.val : ℝ) / q : ℝ) : ℂ) by push_cast; ring]
        exact Complex.ofReal_im _
      rw [Complex.add_im, this, add_zero]; exact hv
    have := (summable_theta_terms h).hasSum
    rw [← theta_eq_tsum] at this
    exact this.mul_left _
  have hs := hasSum_sum (s := Finset.univ) fun a _ => hterm a
  unfold thetaTw
  refine hs.congr_fun fun n => ?_
  unfold gTw
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

end Twisted

end GaloisForLFunctions.RHTower.HalfWeight
