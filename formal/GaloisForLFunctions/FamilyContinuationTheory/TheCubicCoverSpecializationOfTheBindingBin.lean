import GaloisForLFunctions.FamilyContinuationTheory.TheLocalFactorOfThePoissonSeriesIsExplicit
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DirichletBaseChange

/-!
# The cubic cover specialization of the binding bin and general half-plane base-change transfer

Identifying the row sums of the binding bin in the compensated sextic probe against specializations
of rank-two multiple Dirichlet series over `K = ℚ(ω)` isolates three structural obstructions at the
local Euler-factor, residue-character, and norm-shell levels, together with the general-`σ₀`
base-change transfer to `ζ` and Dirichlet `L`-functions:

* **Unramified specialization of the local Poisson row series** (`hasSum_localTerm_zero_X`,
  `hasSum_localTerm_sixthPowerFree`). At any primary prime `π ∤ 6` and unramified row `u ∉ (π)`
  (`j = 0`), setting `X = 0` (removing the inverse witness `1/L(x, η χ̄_u)`) annihilates all eight
  positive-`t` Gauss-sum blocks `baseSum` identically, leaving
  `(1 − V)⁻¹ + χ_π(u) Y (1 − χ_π(u) Y)⁻¹`. Setting `V = 0` (`z → +∞`, isolating sixth-power-free
  row indices `u`) evaluates the local series identically to `(1 − χ_π(u) Y)⁻¹`, the Euler factor
  of the sextic (`n = 6`) Hecke `L`-function `L^{(u)}(w, χ_u)`.
* **Order-`6` vs. cubic (`n = 3`) cover restriction and Hasse–Davenport Gauss obstruction**
  (`two_mul_card_cube_eq_one`, `sextic_cubic_gauss_quadratic_obstruction`,
  `idealRowHom_sq_ideal_eq_cubic`). On any finite group `G`, a homomorphism `φ : G →* ℂ` with
  `φ⁶ = 1` and `φ³ ≠ 1` takes cubic values (`φ(g)³ = 1`) on a subgroup of exact index `2`
  (`2 · #{g : φ(g)³ = 1} = |G|`). At every prime `π ∤ 6` of `ℤ[ω]`, `complexSexticChar` has exact
  order `6`, so cubic specialization holds on half the unit residues locally and globally restricts
  `idealRowHom x (d²)` to the cubic cover character `idealSymbol d x` (`n = 3`) on square ideals
  `u = d²` (`N(d) ≤ U^{1/2}`), while `χ(4) G₁ G₂ = −π |π| Γ(π) ≠ 0` maps sextic–cubic Gauss
  products into the quadratic Gauss phase `Γ(π)`.
* **Linear independence of Dirichlet norm shells** (`dirichlet_norm_shell_linear_independent_real`,
  `dirichlet_norm_shell_linear_independent`). If a finite combination `∑_{n ∈ S} c_n n^{−σ}` over
  positive integers `n ≥ 1` vanishes for all real `σ > 0`, scaling by `(min S)^σ` as `σ → +∞`
  forces `c_n = 0` for all `n ∈ S`. Consequently, polar residues of `1/L(x, η χ̄_u)` cannot cancel
  across distinct norm shells `N(u) = n`, forcing zero-bin partitioning `u ∈ R_δ`.
* **General-`σ₀` base-change transfer to `ζ` and Dirichlet `L`-functions**
  (`dirichlet_halfPlane_of_hecke`, `zeta_halfPlane_of_hecke`,
  `estimate_ladder_payoff_transfers`). For every `σ₀ ≥ 0`, nonvanishing of
  `CubicEisenstein.HeckeFamily.LFunction` on `Re s > σ₀` transfers unconditionally via
  `LFunction (character χ) s = χ.LFunction s · (baseChangeChar χ).LFunction s` to every Dirichlet
  `L`-function `χ.LFunction` (away from `(1, 1)`) and to `riemannZeta` on `Re s > σ₀`, covering the
  entire payoff ladder `σ₀ ∈ {13/15, 5/6, 3/4, 2/3, ½}`.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

/-! ### Finite-group index-two cubic kernel and Dirichlet norm-shell linear independence -/

section NormShellAndGroupObstruction

/-- For any finite group `G` and multiplicative character `φ : G →* ℂ` satisfying `φ⁶ = 1` and
`φ³ ≠ 1`, the cubic-kernel subset `{g ∈ G : φ(g)³ = 1}` has exact cardinality `|G| / 2`. -/
theorem two_mul_card_cube_eq_one {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (φ : G →* ℂ) (h6 : ∀ g : G, φ g ^ 6 = 1) (h3 : ∃ g₀ : G, φ g₀ ^ 3 ≠ 1) :
    2 * (Finset.univ.filter (fun g : G => φ g ^ 3 = 1)).card = Fintype.card G ∧
      (Finset.univ.filter (fun g : G => φ g ^ 3 = 1)).card < Fintype.card G := by
  obtain ⟨g₀, hg₀⟩ := h3
  have hpm : ∀ g : G, φ g ^ 3 = 1 ∨ φ g ^ 3 = -1 := by
    intro g
    refine sq_eq_one_iff.mp ?_
    rw [← pow_mul, h6 g]
  have hg₀_val : φ g₀ ^ 3 = -1 := (hpm g₀).resolve_left hg₀
  set H := Finset.univ.filter (fun g : G => φ g ^ 3 = 1)
  set Hc := Finset.univ.filter (fun g : G => ¬ φ g ^ 3 = 1)
  have hdisj : Disjoint H Hc :=
    Finset.disjoint_left.mpr fun g h1 h2 =>
      (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hunion : H ∪ Hc = Finset.univ := by
    ext g
    simp only [H, Hc, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact em _
  have hsum : H.card + Hc.card = Fintype.card G := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  have himg : H.image (fun g => g₀ * g) = Hc := by
    ext x
    simp only [H, Hc, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [map_mul, mul_pow, hg₀_val, hg, mul_one]
      norm_num
    · intro hx
      have hx_val : φ x ^ 3 = -1 := (hpm x).resolve_left hx
      refine ⟨g₀⁻¹ * x, ?_, mul_inv_cancel_left g₀ x⟩
      rw [map_mul, map_inv, mul_pow, inv_pow, hg₀_val, hx_val]
      norm_num
  have hcard_eq : H.card = Hc.card := by
    rw [← himg, Finset.card_image_of_injective H (mul_right_injective g₀)]
  have hpos : 0 < H.card := Finset.card_pos.mpr ⟨1, by simp [H]⟩
  exact ⟨by omega, by omega⟩

/-- **Real Dirichlet norm-shell linear independence.** A finite real linear combination
`∑_{n ∈ S} c_n n^{−σ}` over positive integers `n ≥ 1` vanishing for all `σ > 0` has identically
zero coefficients. -/
theorem dirichlet_norm_shell_linear_independent_real (S : Finset ℕ)
    (hpos : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℝ)
    (hsum : ∀ σ : ℝ, 0 < σ → ∑ n ∈ S, c n * (n : ℝ) ^ (-σ) = 0) :
    ∀ n ∈ S, c n = 0 := by
  induction hk : S.card generalizing S with
  | zero =>
    obtain rfl := Finset.card_eq_zero.mp hk
    simp
  | succ k ih =>
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set m := S.min' hne
    have hm_mem : m ∈ S := Finset.min'_mem S hne
    have hm1 : 1 ≤ m := hpos m hm_mem
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hscaled : ∀ σ : ℝ, 0 < σ →
        c m + ∑ n ∈ S.erase m, c n * ((m : ℝ) / (n : ℝ)) ^ σ = 0 := by
      intro σ hσ
      have hmul : (m : ℝ) ^ σ * ∑ n ∈ S, c n * (n : ℝ) ^ (-σ) = 0 := by
        rw [hsum σ hσ, mul_zero]
      rw [← Finset.add_sum_erase _ _ hm_mem, mul_add, Finset.mul_sum] at hmul
      have hhead : (m : ℝ) ^ σ * (c m * (m : ℝ) ^ (-σ)) = c m := by
        calc (m : ℝ) ^ σ * (c m * (m : ℝ) ^ (-σ)) =
              c m * ((m : ℝ) ^ σ * (m : ℝ) ^ (-σ)) := by ring
          _ = c m * (m : ℝ) ^ (σ + -σ) := by rw [← Real.rpow_add hm_pos σ (-σ)]
          _ = c m := by simp
      have htail : ∑ n ∈ S.erase m, (m : ℝ) ^ σ * (c n * (n : ℝ) ^ (-σ)) =
          ∑ n ∈ S.erase m, c n * ((m : ℝ) / (n : ℝ)) ^ σ := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 : 1 ≤ n := hpos n (Finset.mem_of_mem_erase hn)
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
        rw [Real.div_rpow hm_pos.le hn_pos.le σ, Real.rpow_neg hn_pos.le σ]
        ring
      rw [hhead, htail] at hmul
      exact hmul
    have htend_cm : Filter.Tendsto
        (fun σ : ℝ => c m + ∑ n ∈ S.erase m, c n * ((m : ℝ) / (n : ℝ)) ^ σ)
        Filter.atTop (nhds (c m)) := by
      have htend_sum : Filter.Tendsto
          (fun σ : ℝ => ∑ n ∈ S.erase m, c n * ((m : ℝ) / (n : ℝ)) ^ σ)
          Filter.atTop (nhds (∑ _n ∈ S.erase m, (0 : ℝ))) := by
        refine tendsto_finset_sum (S.erase m) fun n hn => ?_
        have hmn : m < n :=
          Nat.lt_of_le_of_ne (Finset.min'_le S n (Finset.mem_of_mem_erase hn))
            (Finset.mem_erase.mp hn).1.symm
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
        have hb0 : 0 < (m : ℝ) / (n : ℝ) := div_pos hm_pos hn_pos
        have hb1 : (m : ℝ) / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr (by exact_mod_cast hmn)
        simpa only [mul_zero] using
          (tendsto_rpow_atTop_of_base_lt_one ((m : ℝ) / (n : ℝ)) (by linarith) hb1).const_mul (c n)
      rw [Finset.sum_const_zero] at htend_sum
      simpa only [add_zero] using tendsto_const_nhds.add htend_sum
    have htend_zero : Filter.Tendsto
        (fun σ : ℝ => c m + ∑ n ∈ S.erase m, c n * ((m : ℝ) / (n : ℝ)) ^ σ)
        Filter.atTop (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with σ hσ
      exact (hscaled σ hσ).symm
    have hcm : c m = 0 := tendsto_nhds_unique htend_cm htend_zero
    have herase_sum : ∀ σ : ℝ, 0 < σ → ∑ n ∈ S.erase m, c n * (n : ℝ) ^ (-σ) = 0 := by
      intro σ hσ
      have h := hsum σ hσ
      rw [← Finset.add_sum_erase _ _ hm_mem, hcm, zero_mul, zero_add] at h
      exact h
    have herase_zero := ih (S.erase m) (fun n hn => hpos n (Finset.mem_of_mem_erase hn))
      herase_sum (by rw [Finset.card_erase_of_mem hm_mem, hk]; omega)
    intro n hn
    by_cases hnm : n = m
    · rwa [hnm]
    · exact herase_zero n (Finset.mem_erase.mpr ⟨hnm, hn⟩)

/-- **Complex Dirichlet norm-shell linear independence.** If `∑_{n ∈ S} c_n n^{−σ} = 0` in `ℂ` for
all real `σ > 0` across a finite set `S` of positive integers `n ≥ 1`, then `c_n = 0` for all
`n ∈ S`: inverse-`L` polar residues cannot cancel across distinct row norm shells. -/
theorem dirichlet_norm_shell_linear_independent (S : Finset ℕ)
    (hpos : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℂ)
    (hsum : ∀ σ : ℝ, 0 < σ → ∑ n ∈ S, c n * (n : ℂ) ^ (-(σ : ℂ)) = 0) :
    ∀ n ∈ S, c n = 0 := by
  have hcast : ∀ (n : ℕ) (σ : ℝ), (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro n σ
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ), Complex.ofReal_natCast, Complex.ofReal_neg]
  have hre : ∀ σ : ℝ, 0 < σ → ∑ n ∈ S, (c n).re * (n : ℝ) ^ (-σ) = 0 := by
    intro σ hσ
    have h := congrArg Complex.re (hsum σ hσ)
    simp only [hcast, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.zero_re] at h
    exact h
  have him : ∀ σ : ℝ, 0 < σ → ∑ n ∈ S, (c n).im * (n : ℝ) ^ (-σ) = 0 := by
    intro σ hσ
    have h := congrArg Complex.im (hsum σ hσ)
    simp only [hcast, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero, Complex.zero_im] at h
    exact h
  have hre0 := dirichlet_norm_shell_linear_independent_real S hpos (fun n => (c n).re) hre
  have him0 := dirichlet_norm_shell_linear_independent_real S hpos (fun n => (c n).im) him
  intro n hn
  exact Complex.ext (hre0 n hn) (him0 n hn)

end NormShellAndGroupObstruction

/-! ### Unramified specialization of the corpus local Poisson series and Gauss obstruction -/

section LocalPoisson

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

variable (π : O) [NeZero π] [hP : (Ideal.span {π}).IsMaximal] (hlam : lambda ∉ Ideal.span {π})
  (h2 : (2 : O) ∉ Ideal.span {π}) (hprim : lambda ^ 2 ∣ π - 1)

omit hP in
theorem primeR_zero_X (ηp V : ℂ) : primeR π ηp 0 V = 0 := by
  unfold primeR
  simp

omit [NeZero π] hP in
theorem baseSum_zero_X (ηp Y V : ℂ) (u : O) (j : ℕ) (e p k : Fin 2) :
    baseSum π hlam ηp 0 Y V u j e p k = 0 := by
  fin_cases e <;> fin_cases p <;> fin_cases k <;> simp [baseSum, primeR]

include h2 hprim in
/-- **Specialization of the corpus local Poisson series at `X = 0` (`j = 0`).** Removing the
inverse witness (`X = 0`) kills every Gauss-sum block `baseSum` identically, leaving the `t = 0`
block `(1 − V)⁻¹ + χ_π(u) Y (1 − χ_π(u) Y)⁻¹`. -/
theorem hasSum_localTerm_zero_X (ηp Y V : ℂ) {u : O} (hu : u ∉ Ideal.span {π})
    (hV : ‖V‖ < 1)
    (hW : ‖complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y‖ < 1) :
    HasSum (localTerm π ηp 0 Y V u 0)
      ((1 - V)⁻¹ + complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y *
        (1 - complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y)⁻¹) := by
  have h := hasSum_localTerm π hlam h2 hprim ηp 0 Y V hu (by norm_num) hV hW
    (by rw [primeR_zero_X, norm_zero]; exact zero_lt_one)
  simpa [primeR_zero_X, baseSum_zero_X] using h

include h2 hprim in
/-- **Exact sixth-power-free unramified Euler factor (`X = 0`, `V = 0`, `j = 0`).** At `X = 0` and
`V = 0` (`z → +∞`), the corpus local Poisson series sums identically to `(1 − χ_π(u) Y)⁻¹`, the
local Euler factor of the sextic (`n = 6`) Hecke `L`-function `L^{(u)}(w, χ_u)`. -/
theorem hasSum_localTerm_sixthPowerFree (ηp Y : ℂ) {u : O} (hu : u ∉ Ideal.span {π})
    (hY : ‖Y‖ < 1) :
    HasSum (localTerm π ηp 0 Y 0 u 0)
      (1 - complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u) * Y)⁻¹ := by
  set ρ := complexSexticChar (Ideal.span {π}) hlam (Ideal.Quotient.mk _ u)
  have hρ6 : ρ ^ 6 = 1 := sexticChar_pow_six π hlam _ (unit_mk_of_not_mem π hu)
  have hρ_norm : ‖ρ‖ = 1 := by
    have hp : ‖ρ‖ ^ 6 = 1 := by rw [← norm_pow, hρ6, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ρ) (by norm_num)).mp hp
  have hW : ‖ρ * Y‖ < 1 := by rw [norm_mul, hρ_norm, one_mul]; exact hY
  have h0 := hasSum_localTerm_zero_X π hlam h2 hprim ηp Y 0 hu (by simp) hW
  have hne : 1 - ρ * Y ≠ 0 := by
    intro heq
    have h1 : ρ * Y = 1 := (sub_eq_zero.mp heq).symm
    rw [h1, norm_one] at hW
    exact lt_irrefl 1 hW
  have halg : (1 - (0 : ℂ))⁻¹ + ρ * Y * (1 - ρ * Y)⁻¹ = (1 - ρ * Y)⁻¹ := by
    rw [sub_zero, inv_one]
    field_simp [hne]
    ring
  rwa [halg] at h0

include h2 hprim in
/-- **Local order-`6` vs. order-`3` obstruction and Hasse–Davenport quadratic Gauss shift.** At
every primary prime `π ∤ 6` of `ℤ[ω]`, `complexSexticChar` has non-trivial cube (`χ³ ≠ 1`), takes
cubic values (`χ(u)³ = 1`) on exact half of `(O ⧸ (π))ˣ`, and satisfies
`χ(4) G₁ G₂ = −π |π| Γ(π) ≠ 0`, mapping sextic–cubic Gauss products into the quadratic Gauss phase
`Γ(π)`. -/
theorem sextic_cubic_gauss_quadratic_obstruction :
    complexSexticChar (Ideal.span {π}) hlam ^ 3 ≠ 1 ∧
      2 * (Finset.univ.filter (fun u : (O ⧸ Ideal.span {π})ˣ =>
        complexSexticChar (Ideal.span {π}) hlam (u : O ⧸ Ideal.span {π}) ^ 3 = 1)).card =
        Fintype.card (O ⧸ Ideal.span {π})ˣ ∧
      complexSexticChar (Ideal.span {π}) hlam 4 *
          gaussSum (complexSexticChar (Ideal.span {π}) hlam)
            (principalTraceChar π (NeZero.ne π)) *
          gaussSum (complexSexticChar (Ideal.span {π}) hlam ^ 2)
            (principalTraceChar π (NeZero.ne π)) =
        -ringComplex π * primeAbs π * fixedDualAverage π ∧
      -ringComplex π * primeAbs π * fixedDualAverage π ≠ 0 := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  set χ := complexSexticChar (Ideal.span {π}) hlam
  have hne3 : χ ^ 3 ≠ 1 :=
    mt (complexSexticChar_pow_eq_one_iff π hlam h2 3).mp (by norm_num)
  let φ : (O ⧸ Ideal.span {π})ˣ →* ℂ :=
    { toFun := fun u => χ (u : O ⧸ Ideal.span {π})
      map_one' := by simp
      map_mul' := fun a b => by simp [map_mul] }
  have hφ6 : ∀ u : (O ⧸ Ideal.span {π})ˣ, φ u ^ 6 = 1 :=
    fun u => sexticChar_pow_six π hlam (u : O ⧸ Ideal.span {π}) u.isUnit
  have hφ3 : ∃ u₀ : (O ⧸ Ideal.span {π})ˣ, φ u₀ ^ 3 ≠ 1 := by
    by_contra hall
    push_neg at hall
    apply hne3
    ext x
    by_cases hx : x = 0
    · subst hx
      simp [MulChar.map_zero]
    · have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
      rw [MulChar.pow_apply' χ (by norm_num), MulChar.one_apply hu]
      exact hall hu.unit
  have hcard := (two_mul_card_cube_eq_one φ hφ6 hφ3).1
  have hhd := sextic_gauss_product π hlam h2 hprim
  rw [gauss_three_eq π hlam h2, show (‖ringComplex π‖ : ℂ) = primeAbs π from rfl] at hhd
  have hprod_ne : -ringComplex π * primeAbs π * fixedDualAverage π ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (ringComplex_ne_zero π))
      (norm_ringComplex_ne_zero π)) (fixedDualAverage_prime_ne_zero π h2)
  exact ⟨hne3, hcard, by linear_combination hhd, hprod_ne⟩

end LocalPoisson

/-! ### Square-ideal cubic cover restriction and general-`σ₀` Dirichlet/zeta base-change transfer -/

section CubicRowAndBaseChange

open MetaplecticMobiusDescent.CubicEisenstein

/-- **Global square-row restriction to the cubic cover.** Evaluating the sextic corpus row
character `idealRowHom x` on any square ideal `d²` yields the cubic cover residue symbol
`idealSymbol d x` (`n = 3`). -/
theorem idealRowHom_sq_ideal_eq_cubic (x : Eisenstein.O) (d : Ideal Eisenstein.O) :
    CanonicalRowCompletion.idealRowHom x (d ^ 2) =
      Eisenstein.ringComplex (CubicRamified.idealSymbol d x) := by
  rw [map_pow, CanonicalRowCompletion.idealRowHom_square]

/-- **General-`σ₀` Dirichlet base-change transfer.** For any `σ₀ ≥ 0`, nonvanishing of all
`ℚ(ω)` Hecke `L`-functions `HeckeFamily.LFunction η` on `Re s > σ₀` (off the pole `(1, 1)`)
transfers unconditionally to `χ.LFunction s ≠ 0` on `Re s > σ₀` for every modulus `q ≥ 1` and
Dirichlet character `χ mod q` (away from `(1, 1)`). -/
theorem dirichlet_halfPlane_of_hecke {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), σ₀ < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : σ₀ < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have h := hH (HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

/-- **General-`σ₀` Riemann zeta base-change transfer.** For any `σ₀ ≥ 0`, nonvanishing of
`HeckeFamily.LFunction` on `Re s > σ₀` implies `riemannZeta s ≠ 0` for all `Re s > σ₀`. -/
theorem zeta_halfPlane_of_hecke {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀)
    (hH : ∀ (η : HeckeFamily.Character) (s : ℂ), σ₀ < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0)
    (s : ℂ) (hs : σ₀ < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_halfPlane_of_hecke hσ₀ hH (1 : DirichletCharacter ℂ 1) s hs
    (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

/-- **Payoff ladder transfers (§2.5).** Every step of the producer payoff ladder — `13/15`
(binding-bin row count `(a)`), `5/6` (generic row mean square `(b)`), `3/4` (signed Gram saving
`s = 1/12` in `(c)`), `2/3` (`s = 1/6` in `(c)`), and `½` (`s = 1/3`) — transfers unconditionally
from `ℚ(ω)` Hecke `L`-functions to `riemannZeta` and every `DirichletCharacter.LFunction`. -/
theorem estimate_ladder_payoff_transfers :
    (∀ σ₀ ∈ ({(13 / 15 : ℝ), 5 / 6, 3 / 4, 2 / 3, 1 / 2} : Set ℝ),
      (∀ (η : HeckeFamily.Character) (s : ℂ), σ₀ < s.re →
        (s ≠ 1 ∨ η.residue ≠ 1) → HeckeFamily.LFunction η s ≠ 0) →
      (∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0) ∧
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        σ₀ < s.re → ¬ (χ = 1 ∧ s = 1) → χ.LFunction s ≠ 0)) := by
  intro σ₀ hmem hH
  have hσ₀ : 0 ≤ σ₀ := by
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact ⟨zeta_halfPlane_of_hecke hσ₀ hH,
    fun q _ χ s hs hexc => dirichlet_halfPlane_of_hecke hσ₀ hH χ s hs hexc⟩

end CubicRowAndBaseChange

end GaloisForLFunctions.FamilyContinuationTheory

end
