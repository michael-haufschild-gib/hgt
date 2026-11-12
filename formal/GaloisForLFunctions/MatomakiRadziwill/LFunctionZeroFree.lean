import GaloisForLFunctions.MatomakiRadziwill.LFunctionDLVP
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovZeroFree

/-!
# The Vinogradov–Korobov zero-free region for Dirichlet `L`-functions

For a nonprincipal character `χ` mod `q` there is `γ₀` such that

`L(β + iγ, χ) ≠ 0`  for `γ ≥ γ₀`, `β > 1 − ε(γ)`,  `ε(γ) = θ(log 5γ)/(16000 log log 5γ)`

(`exists_LFunction_ne_zero_vinogradovKorobov_width`), the width of the corpus region for `ζ`
(`Sieve.vinogradovKorobovZeroFreeWidth`, `≥ (log γ)^{-2/3}(log log γ)^{-5/3}/10⁸`).

The growth bound on discs of radius `θ(log 5γ)` about `1 + δ + ih`, `γ ≤ h ≤ 4γ`, is
`‖L(w, ψ)‖ < K_q log 5γ + 1` for every character `ψ` mod `q` (`norm_LFunction_lt_on_disc`):
`norm_LFunction_le_vinogradovKorobov` for `ψ ≠ 1`, and `L(s, 1) = Π_{p|q}(1 − p^{-s}) ζ(s)` with the
corpus disc bound for `ζ` otherwise.  The de la Vallée Poussin inequality (`L_dlvp_inequality`) and
the corpus arithmetic (`Sieve.vk_dlvp_contradiction`) finish as for `ζ`.
-/

open Complex Metric RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {q : ℕ} [NeZero q]

/-- The disc growth constant `K_q = q³ + 56q + qC + 2^q (C_ζ + 1)`. -/
def lGrowthConstant (q : ℕ) : ℝ :=
  ((q : ℝ) ^ 3 + 56 * q + q * hurwitzGrowthConstant) + 2 ^ q * (vinogradovKorobovGrowthConstant + 1)

theorem hurwitzGrowthConstant_nonneg : 0 ≤ hurwitzGrowthConstant := by
  unfold hurwitzGrowthConstant; have := hurwitzBlockConstant_nonneg; linarith

theorem vinogradovKorobovGrowthConstant_nonneg : 0 ≤ vinogradovKorobovGrowthConstant := by
  unfold vinogradovKorobovGrowthConstant vinogradovKorobovBlockConstant; positivity

theorem lGrowthConstant_nonneg (q : ℕ) : 0 ≤ lGrowthConstant q := by
  unfold lGrowthConstant
  have := hurwitzGrowthConstant_nonneg
  have := vinogradovKorobovGrowthConstant_nonneg
  positivity

/-- `‖Π_{p|q} (1 − p^{-w})‖ ≤ 2^q` for `Re w > 0`. -/
theorem norm_prod_one_sub_le {w : ℂ} (hw : 0 < w.re) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))‖ ≤ 2 ^ q := by
  refine (Finset.norm_prod_le _ _).trans ?_
  have hterm : ∀ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-w)‖ ≤ 2 := by
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, show ((p : ℂ)) = (((p : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have : (p : ℝ) ^ (-w).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp1) (by simp; linarith)
    linarith
  calc ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-w)‖ ≤ ∏ _p ∈ q.primeFactors, (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) hterm
    _ = 2 ^ q.primeFactors.card := by rw [Finset.prod_const]
    _ ≤ 2 ^ q := by
        apply pow_le_pow_right₀ (by norm_num)
        calc q.primeFactors.card ≤ (Finset.Icc 1 q).card :=
              Finset.card_le_card fun p hp => Finset.mem_Icc.mpr
                ⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.le_of_mem_primeFactors hp⟩
          _ = q := by simp

/-- **Growth on the discs**, for every character `ψ` mod `q`. -/
theorem norm_LFunction_lt_on_disc (ψ : DirichletCharacter ℂ q) {γ δ h : ℝ}
    (hγ : 2 * Real.exp (Real.exp 30) ≤ γ) (hγq : (q : ℝ) + 1 ≤ γ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hh1 : γ ≤ h) (hh2 : h ≤ 4 * γ) {w : ℂ}
    (hw : w ∈ ball (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I)
      (vinogradovKorobovWidth (Real.log (5 * γ)))) :
    ‖DirichletCharacter.LFunction ψ w‖ < lGrowthConstant q * Real.log (5 * γ) + 1 := by
  set R₀ := vinogradovKorobovWidth (Real.log (5 * γ)) with hR₀
  have hE : (0 : ℝ) < Real.exp (Real.exp 30) := Real.exp_pos _
  have hγ0 : 0 < γ := by linarith
  have hL5 : Real.exp 30 ≤ Real.log (5 * γ) := by
    rw [← Real.log_exp (Real.exp 30)]
    exact Real.log_le_log hE (by linarith)
  have hL51 : (1 : ℝ) ≤ Real.log (5 * γ) := le_trans (Real.one_le_exp (by norm_num)) hL5
  have hR₀0 := vinogradovKorobovWidth_pos hL5
  have hR₀1 : R₀ ≤ 1 / 100 := (vinogradovKorobovWidth_le hL5).trans (by norm_num)
  have hd : ‖w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I)‖ < R₀ := by
    simpa [dist_eq_norm] using hw
  have hre : |w.re - (1 + δ)| < R₀ := by
    have h1 := Complex.abs_re_le_norm (w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I))
    have : (w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I)).re = w.re - (1 + δ) := by simp
    rw [this] at h1; linarith
  have him : |w.im - h| < R₀ := by
    have h1 := Complex.abs_im_le_norm (w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I))
    have : (w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I)).im = w.im - h := by simp
    rw [this] at h1; linarith
  have hre' := abs_lt.mp hre
  have him' := abs_lt.mp him
  have hE1 : (1 : ℝ) ≤ Real.exp (Real.exp 30) := Real.one_le_exp (Real.exp_pos _).le
  have hτlow : Real.exp (Real.exp 30) ≤ w.im := by
    have := him'.1; linarith [hγ, hR₀1, hh1, hE1]
  have hτup : w.im ≤ 5 * γ := by
    have := him'.2; linarith [hγ, hR₀1, hh2, hE1]
  have hτq : (q : ℝ) ≤ w.im := by have := him'.1; linarith
  have hτ0 : 0 < w.im := lt_of_lt_of_le hE hτlow
  have hLτ : Real.exp 30 ≤ Real.log w.im := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log hE hτlow
  have hθ : R₀ ≤ vinogradovKorobovWidth (Real.log w.im) :=
    vinogradovKorobovWidth_anti hLτ (Real.log_le_log hτ0 hτup)
  have hw_eq : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hlog : Real.log w.im ≤ Real.log (5 * γ) := Real.log_le_log hτ0 hτup
  have hCζ := vinogradovKorobovGrowthConstant_nonneg
  have hCh := hurwitzGrowthConstant_nonneg
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  by_cases hψ : ψ = 1
  · subst hψ
    have hwne : w ≠ 1 := by
      intro h1; rw [h1] at hτ0; simp at hτ0
    have hrel := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hwne
    rw [DirichletCharacter.LFunctionTrivChar] at hrel
    rw [hrel, norm_mul]
    have hprod := norm_prod_one_sub_le (q := q) (w := w) (by linarith)
    have hζ := norm_riemannZeta_lt_on_disc hγ hδ0 hδ hh1 hh2 hw
    have h2q : (0 : ℝ) < 2 ^ q := by positivity
    calc ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))‖ * ‖riemannZeta w‖
        ≤ 2 ^ q * (vinogradovKorobovGrowthConstant * Real.log (5 * γ) + 1) :=
          mul_le_mul hprod hζ.le (norm_nonneg _) h2q.le
      _ ≤ 2 ^ q * ((vinogradovKorobovGrowthConstant + 1) * Real.log (5 * γ)) := by
          gcongr; nlinarith
      _ ≤ lGrowthConstant q * Real.log (5 * γ) := by
          unfold lGrowthConstant
          have : 0 ≤ ((q : ℝ) ^ 3 + 56 * q + q * hurwitzGrowthConstant) * Real.log (5 * γ) := by
            positivity
          nlinarith
      _ < lGrowthConstant q * Real.log (5 * γ) + 1 := by linarith
  · have hgrowth := norm_LFunction_le_vinogradovKorobov ψ hψ (τ := w.im) (σ := w.re) hτlow hτq
      (by linarith) (by linarith)
    rw [← hw_eq] at hgrowth
    calc ‖DirichletCharacter.LFunction ψ w‖
        ≤ ((q : ℝ) ^ 3 + 56 * q + q * hurwitzGrowthConstant) * Real.log w.im := hgrowth
      _ ≤ ((q : ℝ) ^ 3 + 56 * q + q * hurwitzGrowthConstant) * Real.log (5 * γ) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ lGrowthConstant q * Real.log (5 * γ) := by
          unfold lGrowthConstant
          have : 0 ≤ 2 ^ q * (vinogradovKorobovGrowthConstant + 1) * Real.log (5 * γ) := by
            positivity
          nlinarith
      _ < lGrowthConstant q * Real.log (5 * γ) + 1 := by linarith

/-- **The Vinogradov–Korobov zero-free region for `L(s, χ)`**, `χ ≠ 1`, with the width `ε(γ)`. -/
theorem exists_LFunction_ne_zero_vinogradovKorobov_width (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    ∃ γ₀ : ℝ, ∀ β γ : ℝ, γ₀ ≤ γ → 1 - vinogradovKorobovZeroFreeWidth γ < β →
      DirichletCharacter.LFunction χ ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  obtain ⟨C, hCdef⟩ : ∃ C, C = lGrowthConstant q := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hCdef]; exact lGrowthConstant_nonneg q
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = max (max 24 (Real.log (C + 1)))
      (max (Real.log 1600001) (3 * max A 0 + 1)) := ⟨_, rfl⟩
  refine ⟨max (max (2 * Real.exp (Real.exp 30)) ((q : ℝ) + 1)) (Real.exp (Real.exp M₀)), ?_⟩
  intro β γ hγ hβ hzero
  have hγ1 : 2 * Real.exp (Real.exp 30) ≤ γ :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hγ
  have hγq : (q : ℝ) + 1 ≤ γ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hγ
  have hγ2 : Real.exp (Real.exp M₀) ≤ γ := le_trans (le_max_right _ _) hγ
  have hE : (0 : ℝ) < Real.exp (Real.exp 30) := Real.exp_pos _
  have hγ0 : 0 < γ := by linarith
  have hβ1 : β ≤ 1 := by
    by_contra hb; push Not at hb
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (s := (β : ℂ) + (γ : ℂ) * Complex.I) (by simp; linarith) hzero
  obtain ⟨L5, hL5def⟩ : ∃ L5, L5 = Real.log (5 * γ) := ⟨_, rfl⟩
  have hL5 : Real.exp 30 ≤ L5 := by
    rw [hL5def, ← Real.log_exp (Real.exp 30)]
    exact Real.log_le_log hE (by linarith)
  have hL50 : 0 < L5 := lt_of_lt_of_le (Real.exp_pos _) hL5
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log L5 := ⟨_, rfl⟩
  have hM30 : 30 ≤ M := by rw [hMdef]; exact one_le_log_of_exp_thirty_le hL5
  have hMM₀ : M₀ ≤ M := by
    have h1 : Real.exp (Real.exp M₀) ≤ 5 * γ := by linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp, ← hL5def] at h2
    have h3 := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp, ← hMdef] at h3
  have hM24 : 24 ≤ M := by
    rw [hM₀] at hMM₀
    linarith [le_max_left (24 : ℝ) (Real.log (C + 1)),
      le_max_left (max 24 (Real.log (C + 1))) (max (Real.log 1600001) (3 * max A 0 + 1))]
  have hMC : Real.log (C + 1) ≤ M := by
    rw [hM₀] at hMM₀
    linarith [le_max_right (24 : ℝ) (Real.log (C + 1)),
      le_max_left (max 24 (Real.log (C + 1))) (max (Real.log 1600001) (3 * max A 0 + 1))]
  have hMK : Real.log 1600001 ≤ M := by
    rw [hM₀] at hMM₀
    linarith [le_max_left (Real.log 1600001) (3 * max A 0 + 1),
      le_max_right (max 24 (Real.log (C + 1))) (max (Real.log 1600001) (3 * max A 0 + 1))]
  have hMA : 3 * max A 0 + 1 ≤ M := by
    rw [hM₀] at hMM₀
    linarith [le_max_right (Real.log 1600001) (3 * max A 0 + 1),
      le_max_right (max 24 (Real.log (C + 1))) (max (Real.log 1600001) (3 * max A 0 + 1))]
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = vinogradovKorobovWidth L5 := ⟨_, rfl⟩
  have hR₀0 : 0 < R₀ := by rw [hR₀]; exact vinogradovKorobovWidth_pos hL5
  have hR₀1 : R₀ ≤ 1 / 100 := by rw [hR₀]; exact (vinogradovKorobovWidth_le hL5).trans (by norm_num)
  obtain ⟨ε, hε⟩ : ∃ ε, ε = R₀ / (16000 * M) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hβε : 1 - ε < β := by
    have e : vinogradovKorobovZeroFreeWidth γ = ε := by
      rw [hε, hR₀, hMdef, hL5def]; rfl
    rw [e] at hβ; exact hβ
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = 7 * ε := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hεsmall : ε ≤ R₀ / 32 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδ16 : δ ≤ 1 / 16 := by rw [hδ]; linarith
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = C * L5 + 1 := ⟨_, rfl⟩
  have hΦ1 : 1 ≤ Φ := by
    rw [hΦ]; have : 0 ≤ C * L5 := by positivity
    linarith
  have hδ2 : δ ≤ 1 / 2 := by linarith
  have hΦa : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) R₀,
      ‖DirichletCharacter.LFunction χ w‖ < Φ := by
    intro w hw
    rw [hR₀, hL5def] at hw
    have := norm_LFunction_lt_on_disc χ hγ1 hγq hδ0 hδ2 le_rfl (by linarith) hw
    rw [hΦ, hCdef, hL5def]; exact this
  have hΦb : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) R₀,
      ‖DirichletCharacter.LFunction (χ ^ 2) w‖ < Φ := by
    intro w hw
    rw [hR₀, hL5def] at hw
    have := norm_LFunction_lt_on_disc (χ ^ 2) hγ1 hγq hδ0 hδ2 (by linarith) (by linarith) hw
    rw [hΦ, hCdef, hL5def]; exact this
  have hgap0 : 0 < 1 + δ - β := by linarith
  have hgap8 : 1 + δ - β < 8 * ε := by rw [hδ]; linarith
  have hclose : 1 + δ - β ≤ R₀ / 2 / 2 := by linarith
  have hγ3 : (3 : ℝ) ≤ γ := by
    have h1 := Real.add_one_le_exp (Real.exp 30)
    have h2 : (1 : ℝ) ≤ Real.exp 30 := Real.one_le_exp (by norm_num)
    linarith
  have hdlvp := L_dlvp_inequality χ hA hγ3 hδ0 hδ16 (R := R₀ / 2)
    (R₀ := R₀) (by linarith) (by linarith) (by linarith) hΦa hΦb hβ1 hclose hzero
  have hlogΦ : Real.log Φ ≤ 2 * M := by
    rw [hΦ, hMdef]
    exact vk_log_Phi_le hC0 (by linarith [Real.add_one_le_exp (30 : ℝ)])
      (by rw [← hMdef]; exact hMC)
  have hlogδ : Real.log (1 + 1 / δ) ≤ 4 * M := by
    rw [hδ, hε, hR₀, hMdef]
    exact vk_log_delta_le hL5 (by rw [← hMdef]; exact hMK)
  have hXb : Real.log Φ + Real.log (1 + 1 / δ) ≤ 6 * M := by linarith
  have hA3 : 3 * A ≤ M / R₀ := by
    have h1 : 3 * A ≤ M := by have := le_max_left A 0; linarith
    have h2 : M ≤ M / R₀ := by
      rw [le_div_iff₀ hR₀0]; nlinarith
    linarith
  exact vk_dlvp_contradiction hR₀0 hM24 hε hδ hA3 hXb hgap0 hgap8 hdlvp

/-- **The Vinogradov–Korobov zero-free region for `L(s, χ)`**, `χ ≠ 1`:
`L(β + iγ, χ) ≠ 0` for `γ ≥ γ₀` and `β > 1 − (log γ)^{-2/3}(log log γ)^{-5/3}/10⁸`. -/
theorem LFunction_ne_zero_vinogradovKorobov (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ γ₀ : ℝ, ∀ β γ : ℝ, γ₀ ≤ γ →
      1 - Real.log γ ^ (-(2 : ℝ) / 3) * Real.log (Real.log γ) ^ (-(5 : ℝ) / 3) / 10 ^ 8 < β →
      DirichletCharacter.LFunction χ ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨γ₀, hγ₀⟩ := exists_LFunction_ne_zero_vinogradovKorobov_width χ hχ
  refine ⟨max γ₀ (Real.exp (Real.exp 30)), fun β γ hγ hβ => ?_⟩
  have hγ1 : γ₀ ≤ γ := le_trans (le_max_left _ _) hγ
  have hγ2 : Real.exp (Real.exp 30) ≤ γ := le_trans (le_max_right _ _) hγ
  have hL : Real.exp 30 ≤ Real.log γ := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hγ2
  have hγ0 : 0 < γ := lt_of_lt_of_le (Real.exp_pos _) hγ2
  exact hγ₀ β γ hγ1 (by linarith [le_vinogradovKorobovZeroFreeWidth hγ0 hL])

end

end GaloisForLFunctions.MatomakiRadziwill
