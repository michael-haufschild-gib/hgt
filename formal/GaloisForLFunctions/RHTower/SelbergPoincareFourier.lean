import GaloisForLFunctions.RHTower.SelbergPoincareSeries
import GaloisForLFunctions.RHTower.SelbergPoincareKernel

open UpperHalfPlane Complex
open scoped MatrixGroups

/-!
# Fourier–Kloosterman expansion of the `Γ(N)` Poincaré series

For `γ ∈ Γ(N)` with bottom row `(c, d)`, `c ≠ 0`: `γz = a/c - 1/(c(cz+d))` (`smul_eq`), so
`Im(γz)^s e(mγz/N) = c^{-2s} e(ma/(cN)) ker_{m/(c²N)}(x + d/c)` (`term_eq`), and `e(ma/(cN))` depends only on
`d̄ = d^{-1} mod |c|N` (`exp_phase_eq`). Cosets of `Γ∞(N)\Γ(N)` correspond to admissible rows `N | c`,
`d ≡ 1 (N)`, `gcd(c,d) = 1` (`range_bot`); for `N ≥ 3` the row `(0, d)` forces `d = 1` (`term_of_c_zero`).

Splitting `d = r + |c|N j` (`tsum_eq_sum_residues`) and applying Poisson summation to each residue class
(`tsum_ker_shift`) gives the `c`-slice `c^{-2s} N^{-s} Σ_n 𝓕ker(n) e(nx/N) S_N(m,n;c)` with the `Γ(N)` Kloosterman
sum `S_N` (`ksum`, `slice`). Hence `P_m(z,s) = Q_m(z,s) = y^s e(mz/N) + Σ_{c≠0} Q_c(z,s)` for `Re s > 1`
(`poincare_eq_Q`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincareFourier
open GaloisForLFunctions.RHTower.SelbergPoincare GaloisForLFunctions.RHTower.SelbergPoincareKernel
open CongruenceSubgroup ModularGroup

/-- `γz = a/c - 1/(c(cz+d))`. -/
theorem smul_eq (γ : SL(2, ℤ)) (z : ℍ) (hc : (γ 1 0 : ℂ) ≠ 0) :
    ((γ • z : ℍ) : ℂ) = (γ 0 0 : ℂ) / (γ 1 0 : ℂ) - 1 / ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1)) := by
  have hdet := γ.2
  rw [Matrix.det_fin_two] at hdet
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdet
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ z
    simpa [UpperHalfPlane.denom] using this
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
  rw [eq_sub_iff_add_eq, div_add_div _ _ hden (mul_ne_zero hc hden), div_eq_div_iff
    (mul_ne_zero hden (mul_ne_zero hc hden)) hc]
  linear_combination -((γ 1 0 : ℂ) * z + γ 1 1) * (γ 1 0 : ℂ) * hdetC


theorem im_smul_eq (γ : SL(2, ℤ)) (z : ℍ) (hc : (γ 1 0 : ℝ) ≠ 0) :
    (γ • z).im = ((γ 1 0 : ℝ) ^ 2)⁻¹ * wt z.im (z.re + (γ 1 1 : ℝ) / (γ 1 0 : ℝ)) := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  have hn : Complex.normSq (UpperHalfPlane.denom γ z) =
      (γ 1 0 : ℝ) ^ 2 * ((z.re + (γ 1 1 : ℝ) / (γ 1 0 : ℝ)) ^ 2 + z.im ^ 2) := by
    simp only [UpperHalfPlane.denom, Complex.normSq_apply]
    simp
    field_simp
  rw [hn, wt]
  field_simp

theorem phase_eq (γ : SL(2, ℤ)) (z : ℍ) (hc : (γ 1 0 : ℝ) ≠ 0) (m N : ℕ) :
    2 * Real.pi * Complex.I * m * ((γ • z : ℍ) : ℂ) / N =
      2 * Real.pi * Complex.I * m * (γ 0 0 : ℂ) / ((γ 1 0 : ℂ) * N) -
      2 * Real.pi * Complex.I * ((m / ((γ 1 0 : ℝ) ^ 2 * N) : ℝ) : ℂ) *
        (wz z.im (z.re + (γ 1 1 : ℝ) / (γ 1 0 : ℝ)))⁻¹ := by
  have hcC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [smul_eq γ z hcC]
  have hw : (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) =
      ((γ 1 0 : ℝ) : ℂ) ^ 2 * wz z.im (z.re + (γ 1 1 : ℝ) / (γ 1 0 : ℝ)) := by
    rw [wz]
    conv_lhs => rw [← UpperHalfPlane.re_add_im z]
    push_cast
    field_simp
    ring
  rw [hw]
  by_cases hN : (N : ℂ) = 0
  · simp [hN]
  have hwz := wz_ne_zero z.im_pos (z.re + (γ 1 1 : ℝ) / (γ 1 0 : ℝ))
  push_cast
  field_simp

/-- **The summand through the kernel.** For `c ≠ 0`,
`Im(γz)^s e(mγz/N) = c^{-2s} e(ma/(cN)) ker_{m/(c²N)}(x + d/c)`. -/
theorem term_eq (N m : ℕ) (s : ℂ) (z : ℍ) (γ : Gamma N) (hc : ((γ : SL(2, ℤ)) 1 0 : ℝ) ≠ 0) :
    term N m s z γ = cexp (-s * (Real.log (((γ : SL(2, ℤ)) 1 0 : ℝ) ^ 2) : ℂ)) *
      cexp (2 * Real.pi * Complex.I * m * ((γ : SL(2, ℤ)) 0 0 : ℂ) / (((γ : SL(2, ℤ)) 1 0 : ℂ) * N)) *
      ker (m / (((γ : SL(2, ℤ)) 1 0 : ℝ) ^ 2 * N)) z.im s
        (z.re + ((γ : SL(2, ℤ)) 1 1 : ℝ) / ((γ : SL(2, ℤ)) 1 0 : ℝ)) := by
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  unfold term ker
  rw [phase_eq g z hc, im_smul_eq g z hc]
  have hw := wt_pos z.im_pos (z.re + (g 1 1 : ℝ) / (g 1 0 : ℝ))
  have hc2 : 0 < (g 1 0 : ℝ) ^ 2 := by positivity
  have hr : 0 < ((g 1 0 : ℝ) ^ 2)⁻¹ * wt z.im (z.re + (g 1 1 : ℝ) / (g 1 0 : ℝ)) := by positivity
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le,
    Real.log_mul (by positivity) hw.ne', Real.log_inv, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Admissible bottom rows of `Γ(N)`: `N | c`, `d ≡ 1 (N)`, `gcd(c, d) = 1`. -/
def adm (N : ℕ) : Set (ℤ × ℤ) := {p | (N : ℤ) ∣ p.1 ∧ ((p.2 : ZMod N) = 1) ∧ IsCoprime p.1 p.2}

variable (N : ℕ)

/-- The bottom row of a coset, as a pair. -/
noncomputable def bot [NeZero N] (q : Cosets N) : ℤ × ℤ :=
  (((Quotient.out q : Gamma N) : SL(2, ℤ)) 1 0, ((Quotient.out q : Gamma N) : SL(2, ℤ)) 1 1)

theorem bot_injective [NeZero N] : Function.Injective (bot N) := by
  intro q q' h
  apply bottom_injective N
  simp only [bot, Prod.mk.injEq] at h
  ext i; fin_cases i <;> simp [bottom, h.1, h.2]

theorem mem_adm_of_mem (γ : Gamma N) : ((γ : SL(2, ℤ)) 1 0, (γ : SL(2, ℤ)) 1 1) ∈ adm N := by
  obtain ⟨_, _, hc, hd⟩ := Gamma_mem.mp γ.2
  have hdet := (γ : SL(2, ℤ)).2
  rw [Matrix.det_fin_two] at hdet
  refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc, hd, ⟨-(γ : SL(2, ℤ)) 0 1, (γ : SL(2, ℤ)) 0 0, ?_⟩⟩
  linear_combination hdet

theorem exists_of_mem_adm {p : ℤ × ℤ} (hp : p ∈ adm N) :
    ∃ γ : Gamma N, (γ : SL(2, ℤ)) 1 0 = p.1 ∧ (γ : SL(2, ℤ)) 1 1 = p.2 := by
  obtain ⟨⟨k, hk⟩, hd, ⟨u, v, huv⟩⟩ := hp
  -- `v d - (-u) c = 1`; shift the top row by `t (c, d)` with `t = u` to make the top-right entry `≡ 0`.
  set a := v + u * p.1
  set b := -u + u * p.2
  have hdet : a * p.2 - b * p.1 = 1 := by simp only [a, b]; linear_combination huv
  let g : SL(2, ℤ) := ⟨!![a, b; p.1, p.2], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  have hd' : (N : ℤ) ∣ p.2 - 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 p.2 N).mp (by simpa using hd.symm)
  have hmem : g ∈ CongruenceSubgroup.Gamma N := by
    rw [Gamma_mem]
    simp only [g, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    obtain ⟨j, hj⟩ := hd'
    have hb : b = u * (N * j) := by simp only [b]; linear_combination u * hj
    refine ⟨?_, ?_, ?_, hd⟩
    · -- `a ≡ 1`: from `a d - b c = 1`, `c ≡ 0`, `d ≡ 1`
      have : (a : ZMod N) * (p.2 : ZMod N) - (b : ZMod N) * (p.1 : ZMod N) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hdet
      rw [hd, hk] at this; push_cast at this; simpa using this
    · rw [hb]; push_cast; simp
    · rw [hk]; push_cast; simp
  exact ⟨⟨g, hmem⟩, rfl, rfl⟩

theorem range_bot [NeZero N] : Set.range (bot N) = adm N := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩; exact mem_adm_of_mem N _
  · intro hp
    obtain ⟨γ, h1, h2⟩ := exists_of_mem_adm N hp
    refine ⟨Quotient.mk _ γ, ?_⟩
    have hrel : QuotientGroup.rightRel (Hinf N) (Quotient.out (Quotient.mk _ γ : Cosets N)) γ :=
      Quotient.exact (Quotient.out_eq _)
    rw [QuotientGroup.rightRel_apply] at hrel
    obtain ⟨k, hk⟩ := mem_Hinf N hrel
    have hγ : ((Quotient.out (Quotient.mk _ γ : Cosets N) : Gamma N) : SL(2, ℤ)) =
        (T ^ ((N : ℤ) * k))⁻¹ * (γ : SL(2, ℤ)) := by
      rw [← hk]; simp
    simp only [bot, hγ, ← zpow_neg, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]

/-- The Kloosterman phase `e(m d̄/(cN))`, `d̄ = d^{-1}` modulo `|c|N`. -/
noncomputable def phase (N m : ℕ) (c d : ℤ) : ℂ :=
  cexp (2 * Real.pi * Complex.I * m * ((((d : ZMod (c.natAbs * N))⁻¹).val : ℕ) : ℂ) / ((c : ℂ) * N))

theorem exp_phase_eq (N m : ℕ) [NeZero N] (γ : Gamma N) (hc : (γ : SL(2, ℤ)) 1 0 ≠ 0) :
    cexp (2 * Real.pi * Complex.I * m * ((γ : SL(2, ℤ)) 0 0 : ℂ) / (((γ : SL(2, ℤ)) 1 0 : ℂ) * N)) =
      phase N m ((γ : SL(2, ℤ)) 1 0) ((γ : SL(2, ℤ)) 1 1) := by
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  set c := g 1 0
  set q := c.natAbs * N
  have hq : q ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hc) (NeZero.ne N)
  haveI : NeZero q := ⟨hq⟩
  obtain ⟨_, hb, _, _⟩ := Gamma_mem.mp γ.2
  have hbN : (N : ℤ) ∣ g 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have hdvd : (q : ℤ) ∣ g 0 0 * g 1 1 - 1 := by
    have : g 0 0 * g 1 1 - 1 = g 0 1 * c := by simp only [c]; linear_combination hdet
    rw [this]
    have hc' : (c.natAbs : ℤ) ∣ c := Int.natAbs_dvd.mpr dvd_rfl
    simpa [q, mul_comm] using mul_dvd_mul hbN hc'
  have hmul : ((g 1 1 : ℤ) : ZMod q) * ((g 0 0 : ℤ) : ZMod q) = 1 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (g 0 0 * g 1 1) q).mpr hdvd
    push_cast at this; rw [mul_comm]; exact this.symm
  have hinv := ZMod.inv_eq_of_mul_eq_one q _ _ hmul
  set abar := ((((g 1 1 : ℤ) : ZMod q))⁻¹).val
  have habar : ((abar : ℤ) : ZMod q) = ((g 0 0 : ℤ) : ZMod q) := by
    simp only [abar]; rw [Int.cast_natCast, ZMod.natCast_zmod_val, hinv]
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).mp habar
  unfold phase
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsgn : ((c.natAbs : ℤ) : ℂ) = (c.sign : ℂ) * c := by
    rw [← Int.sign_mul_self]; push_cast; ring
  have ha : ((g 0 0 : ℤ) : ℂ) = (abar : ℂ) + (q : ℂ) * k := by
    have : (g 0 0 : ℤ) = (abar : ℤ) + q * k := by linear_combination hk
    exact_mod_cast this
  rw [ha]
  have hq' : (q : ℂ) = ((c.natAbs : ℤ) : ℂ) * N := by simp [q]
  rw [show 2 * Real.pi * Complex.I * m * ((abar : ℂ) + (q : ℂ) * k) / ((c : ℂ) * N) =
      2 * Real.pi * Complex.I * m * (abar : ℂ) / ((c : ℂ) * N) + ((m * c.sign * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      rw [hq', hsgn]; push_cast; field_simp,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The identity coset: for `N ≥ 3` a bottom row `(0, d)` of `Γ(N)` has `d = 1`, and the summand is
`y^s e(mz/N)`. -/
theorem term_of_c_zero (N m : ℕ) (hN : 3 ≤ N) (s : ℂ) (z : ℍ) (γ : Gamma N) (hc : (γ : SL(2, ℤ)) 1 0 = 0) :
    term N m s z γ = (z.im : ℂ) ^ s * cexp (2 * Real.pi * Complex.I * m * (z : ℂ) / N) := by
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  obtain ⟨_, hb, _, hd⟩ := Gamma_mem.mp γ.2
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  rw [hc, mul_zero, sub_zero] at hdet
  have hd1 : g 1 1 = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hdet) with h | h
    · exact h
    · exfalso
      have : ((-1 : ℤ) : ZMod N) = 1 := by rw [← h]; exact hd
      have h2 : (N : ℤ) ∣ 2 := by
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp (by simpa using this)
        simpa using this
      have := Int.le_of_dvd (by norm_num) h2
      omega
  have ha1 : g 0 0 = 1 := by rw [hd1, mul_one] at hdet; exact hdet
  obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  have hsz : ((g • z : ℍ) : ℂ) = (z : ℂ) + (N * j : ℤ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    have hj' : g 0 1 = N * j := hj
    simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast, ha1, hc, hd1, hj']
    push_cast; ring
  have him : (g • z).im = z.im := by
    rw [← UpperHalfPlane.coe_im, hsz]; simp
  unfold term
  rw [← hg, him, hsz]
  congr 1
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [show 2 * Real.pi * Complex.I * m * ((z : ℂ) + ((N * j : ℤ) : ℂ)) / N =
      2 * Real.pi * Complex.I * m * (z : ℂ) / N + ((m * j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The summand as a function of the bottom row. -/
noncomputable def F (N m : ℕ) (s : ℂ) (z : ℍ) (p : ℤ × ℤ) : ℂ :=
  if p.1 = 0 then (z.im : ℂ) ^ s * cexp (2 * Real.pi * Complex.I * m * (z : ℂ) / N)
  else cexp (-s * (Real.log ((p.1 : ℝ) ^ 2) : ℂ)) * phase N m p.1 p.2 *
    ker (m / ((p.1 : ℝ) ^ 2 * N)) z.im s (z.re + (p.2 : ℝ) / (p.1 : ℝ))

theorem termQ_eq [NeZero N] (m : ℕ) (hN : 3 ≤ N) (s : ℂ) (z : ℍ) (q : Cosets N) :
    termQ N m s z q = F N m s z (bot N q) := by
  have hq : termQ N m s z q = term N m s z (Quotient.out q) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq, F]
  simp only [bot]
  split_ifs with hc
  · exact term_of_c_zero N m hN s z _ hc
  · rw [term_eq N m s z _ (by exact_mod_cast hc), exp_phase_eq N m _ hc]

theorem poincare_eq_indicator [NeZero N] (m : ℕ) (hN : 3 ≤ N) (s : ℂ) (z : ℍ) :
    poincare N m s z = ∑' p : ℤ × ℤ, (adm N).indicator (F N m s z) p := by
  unfold poincare
  simp_rw [termQ_eq N m hN s z]
  rw [← tsum_range (F N m s z) (bot_injective N), tsum_subtype, range_bot]

theorem summable_indicator [NeZero N] (m : ℕ) (hN : 3 ≤ N) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    Summable ((adm N).indicator (F N m s z)) := by
  have h : Summable (fun q => F N m s z (bot N q)) :=
    (summable_termQ N m hs z).of_norm.congr (fun q => termQ_eq N m hN s z q)
  rw [← (bot_injective N).summable_iff (f := (adm N).indicator (F N m s z))]
  · refine h.congr fun q => ?_
    rw [Function.comp_apply, Set.indicator_of_mem (by rw [← range_bot N]; exact ⟨q, rfl⟩)]
  · intro x hx
    rw [range_bot] at hx
    exact Set.indicator_of_notMem hx _

theorem mem_adm_zero_iff (hN : 3 ≤ N) (d : ℤ) : ((0 : ℤ), d) ∈ adm N ↔ d = 1 := by
  constructor
  · rintro ⟨_, hd, hcop⟩
    have hu : IsUnit d := (isCoprime_zero_left).mp hcop
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · exfalso
      rw [h] at hd
      have h2 : (N : ℤ) ∣ 2 := by
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp (by simpa using hd)
        simpa using this
      have := Int.le_of_dvd (by norm_num) h2
      omega
  · rintro rfl
    exact ⟨dvd_zero _, by simp, isCoprime_zero_left.mpr isUnit_one⟩

theorem slice_zero (m : ℕ) (hN : 3 ≤ N) (s : ℂ) (z : ℍ) :
    ∑' d : ℤ, (adm N).indicator (F N m s z) (0, d) =
      (z.im : ℂ) ^ s * cexp (2 * Real.pi * Complex.I * m * (z : ℂ) / N) := by
  rw [tsum_eq_single 1]
  · rw [Set.indicator_of_mem ((mem_adm_zero_iff N hN 1).mpr rfl), F, if_pos rfl]
  · intro d hd
    exact Set.indicator_of_notMem (fun h => hd ((mem_adm_zero_iff N hN d).mp h)) _

/-- `Fin K × ℤ ≃ ℤ`, `(r, j) ↦ r + K j`. -/
def resEquiv (K : ℕ) (hK : 0 < K) : Fin K × ℤ ≃ ℤ where
  toFun p := (p.1 : ℤ) + K * p.2
  invFun d := (⟨(d % K).toNat, by
    have h1 := Int.emod_nonneg d (by exact_mod_cast hK.ne' : (K : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos d (by exact_mod_cast hK : (0 : ℤ) < K)
    omega⟩, d / K)
  left_inv p := by
    obtain ⟨⟨r, hr⟩, j⟩ := p
    have hK' : (K : ℤ) ≠ 0 := by exact_mod_cast hK.ne'
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hrK : (r : ℤ) < K := by exact_mod_cast hr
    ext
    · simp only
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr0 hrK]; simp
    · simp only
      rw [Int.add_mul_ediv_left _ _ hK', Int.ediv_eq_zero_of_lt hr0 hrK, zero_add]
  right_inv d := by
    have h1 := Int.emod_nonneg d (by exact_mod_cast hK.ne' : (K : ℤ) ≠ 0)
    simp only [Int.toNat_of_nonneg h1]
    exact Int.emod_add_mul_ediv d K

theorem tsum_eq_sum_residues {G : ℤ → ℂ} (hG : Summable G) (K : ℕ) (hK : 0 < K) :
    ∑' d, G d = ∑ r ∈ Finset.range K, ∑' j : ℤ, G (r + K * j) := by
  rw [← (resEquiv K hK).tsum_eq G]
  have hs : Summable (G ∘ resEquiv K hK) := (resEquiv K hK).summable_iff.mpr hG
  rw [show (∑' c, G (resEquiv K hK c)) = ∑' p, (G ∘ resEquiv K hK) p from rfl, Summable.tsum_prod hs,
    tsum_fintype]
  exact Fin.sum_univ_eq_sum_range (fun r => ∑' j : ℤ, G (r + K * j)) K

theorem ker_scale {K β y : ℝ} (hK : 0 < K) (hy : 0 < y) (s : ℂ) (t : ℝ) :
    ker β y s (K * t) = cexp (-s * (Real.log K : ℂ)) * ker (β / K) (y / K) s t := by
  unfold ker
  have hw : wt y (K * t) = K⁻¹ * wt (y / K) t := by
    unfold wt; field_simp
  have hKC : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hz : wz y (K * t) = (K : ℂ) * wz (y / K) t := by
    unfold wz; push_cast; field_simp
  rw [hw, Real.log_mul (inv_ne_zero hK.ne') (wt_pos (by positivity) t).ne', Real.log_inv, hz,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem summable_norm_fourier_ker {β y : ℝ} {s : ℂ} (hβ : 0 ≤ β) (hy : 0 < y) (hs : 1 / 2 < s.re) :
    Summable (fun n : ℤ => ‖FourierTransform.fourier (ker β y s) n‖) := by
  set C := dconst β y s * (y ^ (1 - s.re) * cst s.re) / (2 * Real.pi) ^ 2
  have hsum : Summable (fun n : ℤ => C * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left C
  refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => C * (1 / (n : ℝ) ^ 2)) hsum ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_le] at hn
  by_contra h0
  apply hn.not_ge
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h0
  have h := norm_fourier_ker_le_sq hβ hy hs n
  rw [norm_norm]
  have hpos : 0 < (2 * Real.pi * |(n : ℝ)|) ^ 2 := by positivity
  rw [show C * (1 / (n : ℝ) ^ 2) = dconst β y s * (y ^ (1 - s.re) * cst s.re) / (2 * Real.pi * |(n : ℝ)|) ^ 2 by
    simp only [C]; rw [mul_pow, mul_pow, sq_abs]; field_simp]
  rw [le_div_iff₀ hpos, mul_comm]
  exact h

theorem natAbs_mul_eq (c : ℤ) (N : ℕ) : ((c.natAbs * N : ℕ) : ℤ) = c * (c.sign * N) := by
  push_cast
  rw [← Int.natCast_natAbs, ← Int.sign_mul_self c]; ring

theorem adm_shift {c : ℤ} (r j : ℤ) :
    (c, r + ((c.natAbs * N : ℕ) : ℤ) * j) ∈ adm N ↔ (c, r) ∈ adm N := by
  simp only [adm, Set.mem_setOf_eq]
  rw [natAbs_mul_eq]
  have hN : ((((c * (c.sign * N) * j : ℤ)) : ZMod N)) = 0 := by
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _)]
    exact Dvd.intro (c * c.sign * j) (by ring)
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · push_cast at h2 hN; rw [← h2]; linear_combination -hN
    · have : r = (r + c * (c.sign * N) * j) + c * (-(c.sign * N * j)) := by ring
      rw [this]; exact h3.add_mul_left_right _
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · push_cast at h2 hN ⊢; rw [← h2]; linear_combination hN
    · rw [show r + c * (c.sign * N) * j = r + c * (c.sign * N * j) by ring]
      exact h3.add_mul_left_right _

theorem phase_shift (m : ℕ) (c r j : ℤ) :
    phase N m c (r + ((c.natAbs * N : ℕ) : ℤ) * j) = phase N m c r := by
  have h : (((r + ((c.natAbs * N : ℕ) : ℤ) * j : ℤ)) : ZMod (c.natAbs * N)) = (r : ZMod (c.natAbs * N)) := by
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  unfold phase
  rw [h]

theorem arg_shift {c : ℤ} (hc : c ≠ 0) (x : ℝ) (r j : ℤ) :
    x + (((r + ((c.natAbs * N : ℕ) : ℤ) * j : ℤ)) : ℝ) / (c : ℝ) =
      x + (r : ℝ) / c + N * ((c.sign * j : ℤ) : ℝ) := by
  rw [natAbs_mul_eq]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp
  ring

theorem tsum_sign {c : ℤ} (hc : c ≠ 0) (f : ℤ → ℂ) : ∑' j : ℤ, f (c.sign * j) = ∑' j : ℤ, f j := by
  rcases lt_or_gt_of_ne hc with h | h
  · simp only [Int.sign_eq_neg_one_of_neg h, neg_mul, one_mul]
    exact (Equiv.neg ℤ).tsum_eq f
  · simp [Int.sign_eq_one_of_pos h]

/-- **Poisson summation with period `N`**: `Σ_j ker(x' + Nj) = N^{-s} Σ_n 𝓕ker_{β/N, y/N}(n) e(nx'/N)`. -/
theorem tsum_ker_shift {β y : ℝ} {s : ℂ} (hβ : 0 ≤ β) (hy : 0 < y) (hs : 3 / 4 ≤ s.re) (hN : 0 < N)
    (x' : ℝ) :
    ∑' j : ℤ, ker β y s (x' + N * j) = cexp (-s * (Real.log N : ℂ)) *
      ∑' n : ℤ, FourierTransform.fourier (ker (β / N) (y / N) s) n *
        cexp (2 * Real.pi * Complex.I * n * x' / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∀ j : ℤ, ker β y s (x' + N * j) =
      cexp (-s * (Real.log N : ℂ)) * ker (β / N) (y / N) s (x' / N + j) := by
    intro j
    rw [← ker_scale hN' hy s]
    congr 1; field_simp
  simp_rw [h1]
  rw [tsum_mul_left, tsum_ker_eq_tsum_fourier (div_nonneg hβ hN'.le) (div_pos hy hN') hs]
  congr 1
  apply tsum_congr
  intro n
  rw [fourier_coe_apply]
  congr 2
  push_cast
  field_simp

/-- The summand of the `Γ(N)` Kloosterman sum: `e(m d̄/(cN)) e(nd/(cN))`. -/
noncomputable def kphase (N m : ℕ) (n : ℤ) (p : ℤ × ℤ) : ℂ :=
  phase N m p.1 p.2 * cexp (2 * Real.pi * Complex.I * n * p.2 / ((p.1 : ℂ) * N))

/-- The `Γ(N)` Kloosterman sum `S_N(m, n; c) = Σ_{d mod |c|N, (c,d) admissible} e((m d̄ + n d)/(cN))`. -/
noncomputable def ksum (N m : ℕ) (c n : ℤ) : ℂ :=
  ∑ r ∈ Finset.range (c.natAbs * N), (adm N).indicator (kphase N m n) (c, r)

theorem norm_cexp_two_pi_I_real (t : ℝ) : ‖cexp (2 * Real.pi * Complex.I * t)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- **The `c`-slice of the Poincaré series** (`c ≠ 0`): Poisson summation over `d ≡ r (mod |c|N)`. -/
theorem slice (m : ℕ) [NeZero N] {c : ℤ} (hc : c ≠ 0) {s : ℂ} (hs : 3 / 4 ≤ s.re) (z : ℍ)
    (hsum : Summable fun d : ℤ => (adm N).indicator (F N m s z) (c, d)) :
    ∑' d : ℤ, (adm N).indicator (F N m s z) (c, d) =
      cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
        ∑' n : ℤ, FourierTransform.fourier (ker (m / ((c : ℝ) ^ 2 * N) / N) (z.im / N) s) n *
          cexp (2 * Real.pi * Complex.I * n * z.re / N) * ksum N m c n := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hK : 0 < c.natAbs * N := Nat.mul_pos (Int.natAbs_pos.mpr hc) hN
  have hβ : 0 ≤ (m : ℝ) / ((c : ℝ) ^ 2 * N) := by positivity
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set β := (m : ℝ) / ((c : ℝ) ^ 2 * N)
  set E := cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ))
  set EN := cexp (-s * (Real.log N : ℂ))
  set Fh : ℤ → ℂ := fun n => FourierTransform.fourier (ker (β / N) (z.im / N) s) n
  have hFs : Summable fun n => ‖Fh n‖ :=
    summable_norm_fourier_ker (div_nonneg hβ (Nat.cast_nonneg N)) (div_pos z.im_pos (by exact_mod_cast hN)) (by linarith)
  rw [tsum_eq_sum_residues hsum _ hK]
  have hr : ∀ r ∈ Finset.range (c.natAbs * N),
      ∑' j : ℤ, (adm N).indicator (F N m s z) (c, (r : ℤ) + ((c.natAbs * N : ℕ) : ℤ) * j) =
        E * EN * ∑' n : ℤ, Fh n * cexp (2 * Real.pi * Complex.I * n * z.re / N) *
          (adm N).indicator (kphase N m n) (c, r) := by
    intro r _
    by_cases hmem : (c, (r : ℤ)) ∈ adm N
    · have hterm : ∀ j : ℤ, (adm N).indicator (F N m s z) (c, (r : ℤ) + ((c.natAbs * N : ℕ) : ℤ) * j) =
          E * phase N m c r * ker β z.im s (z.re + (r : ℝ) / c + N * ((c.sign * j : ℤ) : ℝ)) := by
        intro j
        rw [Set.indicator_of_mem ((adm_shift N r j).mpr hmem), F, if_neg hc, phase_shift N m c r j]
        simp only
        rw [arg_shift N hc]
        push_cast
        rfl
      simp_rw [hterm]
      rw [tsum_mul_left, tsum_sign hc (fun j => ker β z.im s (z.re + (r : ℝ) / c + N * (j : ℝ))),
        tsum_ker_shift N hβ z.im_pos hs hN]
      simp_rw [Set.indicator_of_mem hmem, kphase]
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [Fh]
      have hsplit : cexp (2 * Real.pi * Complex.I * n * ((z.re + (r : ℝ) / c : ℝ) : ℂ) / N) =
          cexp (2 * Real.pi * Complex.I * n * z.re / N) * cexp (2 * Real.pi * Complex.I * n * (r : ℤ) / ((c : ℂ) * N)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; field_simp
      rw [hsplit]
      ring
    · have h0 : ∀ j : ℤ, (adm N).indicator (F N m s z) (c, (r : ℤ) + ((c.natAbs * N : ℕ) : ℤ) * j) = 0 :=
        fun j => Set.indicator_of_notMem (fun h => hmem ((adm_shift N r j).mp h)) _
      simp_rw [h0, Set.indicator_of_notMem hmem, mul_zero, tsum_zero, mul_zero]
  rw [Finset.sum_congr rfl hr, ← Finset.mul_sum]
  congr 1
  have hsum_n : ∀ r ∈ Finset.range (c.natAbs * N), Summable fun n : ℤ =>
      Fh n * cexp (2 * Real.pi * Complex.I * n * z.re / N) * (adm N).indicator (kphase N m n) (c, r) := by
    intro r _
    refine Summable.of_norm_bounded (g := fun n => ‖Fh n‖) hFs (fun n => ?_)
    rw [norm_mul, norm_mul]
    have h1 : ‖cexp (2 * Real.pi * Complex.I * n * z.re / N)‖ = 1 := by
      rw [show 2 * Real.pi * Complex.I * n * z.re / N = 2 * Real.pi * Complex.I * ((n * z.re / N : ℝ) : ℂ) by
        push_cast; ring]
      exact norm_cexp_two_pi_I_real _
    have h2 : ‖(adm N).indicator (kphase N m n) (c, r)‖ ≤ 1 := by
      by_cases hmem : (c, (r : ℤ)) ∈ adm N
      · rw [Set.indicator_of_mem hmem, kphase, norm_mul, phase]
        rw [show 2 * Real.pi * Complex.I * m * ((((r : ℤ) : ZMod (c.natAbs * N))⁻¹.val : ℕ) : ℂ) / ((c : ℂ) * N) =
            2 * Real.pi * Complex.I * ((m * (((r : ℤ) : ZMod (c.natAbs * N))⁻¹.val : ℕ) / (c * N) : ℝ) : ℂ) by
            push_cast; ring,
          show 2 * Real.pi * Complex.I * n * (r : ℤ) / ((c : ℂ) * N) =
            2 * Real.pi * Complex.I * ((n * r / (c * N) : ℝ) : ℂ) by push_cast; ring,
          norm_cexp_two_pi_I_real, norm_cexp_two_pi_I_real, one_mul]
      · rw [Set.indicator_of_notMem hmem, norm_zero]; norm_num
    rw [h1, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) h2
  rw [← Summable.tsum_finsetSum hsum_n]
  apply tsum_congr
  intro n
  rw [ksum, Finset.mul_sum]

/-- The `c`-th term of the continued Poincaré series (zero for `c = 0`). -/
noncomputable def Qc (N m : ℕ) (s : ℂ) (z : ℍ) (c : ℤ) : ℂ :=
  if c = 0 then 0 else
    cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ)) * cexp (-s * (Real.log N : ℂ)) *
      ∑' n : ℤ, FourierTransform.fourier (ker (m / ((c : ℝ) ^ 2 * N) / N) (z.im / N) s) n *
        cexp (2 * Real.pi * Complex.I * n * z.re / N) * ksum N m c n

/-- The Fourier–Kloosterman form `Q_m(z, s) = y^s e(mz/N) + Σ_{c ≠ 0} Q_c(z, s)`. -/
noncomputable def Q (N m : ℕ) (s : ℂ) (z : ℍ) : ℂ :=
  (z.im : ℂ) ^ s * cexp (2 * Real.pi * Complex.I * m * (z : ℂ) / N) + ∑' c : ℤ, Qc N m s z c

/-- **Fourier–Kloosterman expansion** of the Poincaré series for `Re s > 1`, `N ≥ 3`. -/
theorem poincare_eq_Q [NeZero N] (m : ℕ) (hN : 3 ≤ N) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    poincare N m s z = Q N m s z := by
  have hsum := summable_indicator N m hN hs z
  rw [poincare_eq_indicator N m hN s z, Summable.tsum_prod hsum,
    Summable.tsum_eq_add_tsum_ite hsum.prod 0, slice_zero N m hN s z, Q]
  congr 1
  apply tsum_congr
  intro c
  by_cases hc : c = 0
  · rw [if_pos hc, Qc, if_pos hc]
  · rw [if_neg hc, Qc, if_neg hc, slice N m hc (by linarith) z (hsum.prod_factor c)]

end GaloisForLFunctions.RHTower.SelbergPoincareFourier
