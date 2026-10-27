import GaloisForLFunctions.BiarithmeticGaugeGeometry.StrongMultiplicityOneBelowTheSquareRootDeficit

/-!
# Strong Multiplicity One for Powers of ζ

`CompletedPositiveSystem κ d` collects the `F` holomorphic and zero-free on `Re s > 1` with positive
definite vertical sections of `−F'/F`, whose completion `Λ = (s(s−1))^κ Γ_ℝ(s)^d F` is entire of
order one, symmetric and real. Its base member of degree `d` is `ζ^d`, with completion
`(s(s−1))^{κ−d}(2ξ)^d`. This module compares an arbitrary member with `ζ^d` through the
Landau–Wronskian principle. Since `ξ` has no real zero, the anchor of a nonnegative prime-side excess
can only sit on the pole budget at `s = 1`; without pole budget it does not exist. Unlike the
height-coupled case no hypothesis on the zeros of `ξ` enters.

* **Orders and anchor (`zetaPowDeformation_orders_and_anchor`).** If `−F'/F + dζ'/ζ = 𝓛ν + E` with
  `ν ≥ 0` and `E` holomorphic on `Re s > σ_E`, then `Λ (s(s−1))^{d−κ}` and `(s(s−1))^{κ−d}(2ξ)^d`
  have the same divisor on `Re w > max(c, σ_E)`, and an anchor `c > max(0, σ_E)` forces `d < κ`
  and `c ∈ {0, 1}`.
* **Rigidity without pole budget (`zetaPowDeformation_trivial`).** If `κ ≤ d` and `σ_E < ½`, then
  `κ = d` and `F = K ζ^d` with `K ∈ ℝ^×`: the divisor of `Λ` is that of `(2ξ)^d` (right of `½` by the
  principle, left of it by the functional equation) and divisor rigidity applies.
* **Strong multiplicity one (`latticeMember_eq_zetaPow`).** A member with `−F'/F = Σ b(n) n^{−s}`,
  `b ≥ 0`, `κ ≤ d`, whose deficit `Σ (dΛ(n) − b(n))⁺ n^{−s}` has abscissa `< ½`, has `κ = d`,
  `b(n) = dΛ(n)` for every `n ≥ 1`, and `F = K ζ^d`. Any surplus is allowed.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing MultiplicativePositivityGeometry
  HTGeometry
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass laplaceMass_antitone)

/-- Two functions sharing a nonvanishing factor near `s` have the same difference of logarithmic
derivatives as their cofactors. -/
theorem logDeriv_sub_eq_of_common_factor {f g P A B : ℂ → ℂ} {s : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 s) (hf : ∀ w ∈ U, f w = P w * A w) (hg : ∀ w ∈ U, g w = P w * B w)
    (hP : P s ≠ 0) (hA : A s ≠ 0) (hB : B s ≠ 0) (hPd : DifferentiableAt ℂ P s)
    (hAd : DifferentiableAt ℂ A s) (hBd : DifferentiableAt ℂ B s) :
    logDeriv g s - logDeriv f s = logDeriv B s - logDeriv A s := by
  have hf' : f =ᶠ[𝓝 s] fun w => P w * A w := Filter.eventually_of_mem hU hf
  have hg' : g =ᶠ[𝓝 s] fun w => P w * B w := Filter.eventually_of_mem hU hg
  rw [logDeriv_apply, logDeriv_apply, hf'.deriv_eq, hg'.deriv_eq, hf'.eq_of_nhds, hg'.eq_of_nhds,
    ← logDeriv_apply, ← logDeriv_apply, logDeriv_mul s hP hA hPd hAd, logDeriv_mul s hP hB hPd hBd]
  ring

/-- **Orders and the anchor of a deformation of `ζ^d`.** If `(F, Λ) ∈ CompletedPositiveSystem κ d`
and `−F'/F + dζ'/ζ = 𝓛ν + E` on a real ray, then for some `c ≥ 0` the completions
`Λ (s(s−1))^{d−κ}` and `(s(s−1))^{κ−d}(2ξ)^d` have the same order at every `Re w > max(c, σ_E)`,
if `c > max(0, σ_E)` then `d < κ` and `c = 1`; the Landau–Wronskian relation holds on
`Re z > max(c, σ_E)` and the Laplace kernel of `ν` is integrable on `Re z > c`. -/
theorem zetaPowDeformation_orders_and_anchor {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ}
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (fun s => riemannZeta s ^ d) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) :
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ w : ℂ, max c σE < w.re →
        analyticOrderAt (fun s => Λ s * (s * (s - 1)) ^ (d - κ)) w =
          analyticOrderAt (fun s => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d) w) ∧
      (0 < c → σE < c → d < κ ∧ c = 1) ∧
      (∀ z : ℂ, max c σE < z.re → Λ z * (z * (z - 1)) ^ (d - κ) ≠ 0 →
        (z * (z - 1)) ^ (κ - d) * (2 * RHTower.xi z) ^ d ≠ 0 →
        logDeriv (fun s => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d) z -
          logDeriv (fun s => Λ s * (s * (s - 1)) ^ (d - κ)) z =
          GaloisForLFunctions.RHTower.complexLaplace ν z + E z) ∧
      (∀ z : ℂ, c < z.re →
        Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ)))) := by
  have hZ := completedPositiveSystem_riemannZeta
  set Λ' : ℂ → ℂ := fun s => Λ s * (s * (s - 1)) ^ (d - κ) with hΛ'
  set Λ₀ : ℂ → ℂ := fun s => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d with hΛ₀
  have hΛ'd : Differentiable ℂ Λ' := hS.entire_Λ.mul (by fun_prop)
  have hΛ₀d : Differentiable ℂ Λ₀ := zetaPow_base_differentiable κ d
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs01 : ∀ s : ℂ, 1 < s.re → s * (s - 1) ≠ 0 := fun s hs => mul_ne_zero
    (fun h => by rw [h, Complex.zero_re] at hs; linarith)
    (sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith)
  -- common archimedean factor `P = (s(s−1))^{κ + (d−κ)} Γ_ℝ^d` on `Re s > 1`
  set P : ℂ → ℂ := fun s => (s * (s - 1)) ^ (κ + (d - κ)) * Complex.Gammaℝ s ^ d with hPdef
  have hΛ'P : ∀ w ∈ {w : ℂ | 1 < w.re}, Λ' w = P w * F w := fun w hw => by
    simp only [hΛ', hPdef, hS.completed_eq w hw, pow_add]; ring
  have hΛ₀P : ∀ w ∈ {w : ℂ | 1 < w.re}, Λ₀ w = P w * riemannZeta w ^ d := fun w hw => by
    have hξ : 2 * RHTower.xi w = w * (w - 1) * Complex.Gammaℝ w * riemannZeta w := by
      simpa using hZ.completed_eq w hw
    show (w * (w - 1)) ^ (κ - d) * (2 * RHTower.xi w) ^ d =
      (w * (w - 1)) ^ (κ + (d - κ)) * Complex.Gammaℝ w ^ d * riemannZeta w ^ d
    rw [hξ, show κ + (d - κ) = (κ - d) + d by omega]
    simp only [mul_pow]
    ring
  have hPne : ∀ s : ℂ, 1 < s.re → P s ≠ 0 := fun s hs =>
    mul_ne_zero (pow_ne_zero _ (hs01 s hs))
      (pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)))
  have hζne : ∀ s : ℂ, 1 < s.re → riemannZeta s ^ d ≠ 0 := fun s hs =>
    pow_ne_zero d (riemannZeta_ne_zero_of_one_lt_re hs)
  have hΛ'ne : ∀ s : ℂ, 1 < s.re → Λ' s ≠ 0 := fun s hs => by
    rw [hΛ'P s hs]; exact mul_ne_zero (hPne s hs) (hS.ne_zero_F s hs)
  have hΛ₀ne : ∀ s : ℂ, 1 < s.re → Λ₀ s ≠ 0 := fun s hs => by
    rw [hΛ₀P s hs]; exact mul_ne_zero (hPne s hs) (hζne s hs)
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  obtain ⟨c, hc0, hord, hanchor, hrel, hint⟩ := landauWronskian_orders_and_anchor hΛ'd hΛ₀d
    (analyticOrderAt_ne_top_of_ne_zero hΛ'd (hΛ'ne 2 h2))
    (analyticOrderAt_ne_top_of_ne_zero hΛ₀d (hΛ₀ne 2 h2)) (σ₁ := max σ₁ 1)
    (ne_top_of_le_ne_top hconv (laplaceMass_antitone ν (le_max_left σ₁ 1))) hE
    (fun σ hσ => by
      have hσ1 : 1 < (σ : ℂ).re := by simpa using lt_of_le_of_lt (le_max_right _ _) hσ
      refine ⟨hΛ'ne σ hσ1, hΛ₀ne σ hσ1, ?_⟩
      rw [logDeriv_sub_eq_of_common_factor (hU.mem_nhds hσ1) hΛ'P hΛ₀P (hPne σ hσ1)
        (hS.ne_zero_F σ hσ1) (hζne σ hσ1)
        (((by fun_prop : Differentiable ℂ fun s : ℂ => (s * (s - 1)) ^ (κ + (d - κ))) σ).mul
          ((GaloisForLFunctions.differentiableAt_Gammaℝ (by linarith)).pow d))
        ((hS.diffOn_F σ hσ1).differentiableAt (hU.mem_nhds hσ1))
        ((differentiableAt_riemannZeta fun h => by
          rw [h, Complex.one_re] at hσ1; linarith).pow d),
        ← hagree σ (lt_of_le_of_lt (le_max_left _ _) hσ)]
      ring)
  refine ⟨c, hc0, hord, fun hcpos hcE => ?_, hrel, hint⟩
  have h := (zetaPow_base_real_zero (hanchor hcpos hcE).1)
  refine ⟨h.1, h.2.resolve_left hcpos.ne'⟩

/-- `(2ξ)^d` has an order-one envelope. -/
theorem orderOneEnvelope_two_xi_pow (d : ℕ) : OrderOneEnvelope fun s => (2 * RHTower.xi s) ^ d := by
  induction d with
  | zero => simpa using orderOneEnvelope_const (1 : ℂ)
  | succ d ih =>
    exact (ih.mul completedPositiveSystem_riemannZeta.orderOne_Λ).congr fun s => by
      simp only [pow_succ]

/-- **Rigidity of `ζ^d` without pole budget.** If `(F, Λ) ∈ CompletedPositiveSystem κ d` with
`κ ≤ d` and `−F'/F + dζ'/ζ = 𝓛ν + E` with `ν ≥ 0` and `E` holomorphic on `Re s > σ_E`, `σ_E < ½`,
then `κ = d` and `F = K ζ^d` for a nonzero real `K`. -/
theorem zetaPowDeformation_trivial {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (hκ : κ ≤ d) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (fun s => riemannZeta s ^ d) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) :
    κ = d ∧ ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * riemannZeta s ^ d := by
  have hZ := completedPositiveSystem_riemannZeta
  have hξd : Differentiable ℂ fun s => (2 * RHTower.xi s) ^ d := fun s => (hZ.entire_Λ s).pow d
  obtain ⟨c, hc0, hord, hanchor, -, -⟩ := zetaPowDeformation_orders_and_anchor hS hconv hE hagree
  have hmax : max c σE < 1 / 2 := by
    rcases le_or_gt c 0 with hc | hc
    · exact max_lt (by linarith) hσE
    · rcases le_or_gt c σE with hcE | hcE
      · exact max_lt (by linarith) hσE
      · exact absurd (hanchor hc hcE).1 (by omega : ¬ d < κ)
  have hκd0 : κ - d = 0 := by omega
  -- no pole budget: `κ = d`, read off at `s = 1`
  have hκd : κ = d := by
    by_contra hne
    have hdk : d - κ ≠ 0 := by omega
    have h1 := hord 1 (by simp only [Complex.one_re]; linarith)
    simp only [hκd0, pow_zero, one_mul] at h1
    have hξ1 : (2 * RHTower.xi (1 : ℂ)) ^ d ≠ 0 :=
      pow_ne_zero d (mul_ne_zero two_ne_zero (by simpa using RHTower.xi_ne_zero_of_real 1))
    rw [(hξd.analyticAt 1).analyticOrderAt_eq_zero.mpr hξ1] at h1
    have hz : (fun s => Λ s * (s * (s - 1)) ^ (d - κ)) 1 = 0 := by simp [zero_pow hdk]
    exact ((hS.entire_Λ.mul (by fun_prop : Differentiable ℂ
      fun s : ℂ => (s * (s - 1)) ^ (d - κ))).analyticAt 1).analyticOrderAt_eq_zero.mp h1 hz
  subst hκd
  simp only [Nat.sub_self, pow_zero, mul_one, one_mul] at hord
  -- the divisor of `Λ` is that of `(2ξ)^d`: right of `½` directly, left of it by symmetry
  have hsym₀ : ∀ s, (2 * RHTower.xi (1 - s)) ^ κ = (2 * RHTower.xi s) ^ κ := fun s => by
    rw [RHTower.xi_one_sub]
  have hordall : ∀ w : ℂ, analyticOrderAt Λ w = analyticOrderAt (fun s => (2 * RHTower.xi s) ^ κ) w := by
    intro w
    rcases lt_or_ge (max c σE) w.re with hw | hw
    · exact hord w hw
    · have h1 : max c σE < (1 - w).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      have h := hord (1 - w) h1
      rw [hS.orderAt_one_sub] at h
      rw [h]
      have h' := RHTower.analyticOrderAt_comp_one_sub hξd (1 - w)
      rw [sub_sub_cancel, show (fun s => (2 * RHTower.xi (1 - s)) ^ κ) =
        fun s => (2 * RHTower.xi s) ^ κ from funext hsym₀] at h'
      exact h'.symm
  obtain ⟨K, hK0, hK⟩ := eq_real_const_mul_of_orders_eq hS.entire_Λ hξd
    hS.orderOne_Λ (orderOneEnvelope_two_xi_pow κ) hS.sym_Λ hsym₀ hS.conj_Λ
    (fun s => by
      show (2 * RHTower.xi (starRingEnd ℂ s)) ^ κ = starRingEnd ℂ ((2 * RHTower.xi s) ^ κ)
      rw [map_pow]
      congr 1
      exact hZ.conj_Λ s)
    (fun s hs => pow_ne_zero κ (hZ.ne_zero_of_one_lt_re hs)) hordall
  refine ⟨rfl, K, hK0, fun s hs => ?_⟩
  -- cancel the common archimedean factor
  have hξ : 2 * RHTower.xi s = s * (s - 1) * Complex.Gammaℝ s * riemannZeta s := by
    simpa using hZ.completed_eq s hs
  have hξκ : (2 * RHTower.xi s) ^ κ =
      ((s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ κ) * riemannZeta s ^ κ := by
    rw [hξ, mul_pow, mul_pow]
  have hP : (s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ κ ≠ 0 := fun h =>
    pow_ne_zero κ (hZ.ne_zero_of_one_lt_re hs) (by rw [hξκ, h, zero_mul])
  refine mul_left_cancel₀ hP ?_
  have hKs : Λ s = K * (2 * RHTower.xi s) ^ κ := hK s
  rw [← hS.completed_eq s hs, hKs, hξκ]
  ring

/-- **Strong multiplicity one for `ζ^d`.** Let `(F, Λ) ∈ CompletedPositiveSystem κ d` with `κ ≤ d` and
`−F'/F = Σ b(n) n^{−s}`, `b ≥ 0`. If the deficit `Σ (dΛ(n) − b(n))⁺ n^{−s}` has abscissa `< ½`, then
`κ = d`, `b(n) = dΛ(n)` for every `n ≥ 1`, and `F = K ζ^d` with `K ∈ ℝ^×`. -/
theorem latticeMember_eq_zetaPow {κ d : ℕ} {F Λ : ℂ → ℂ} (hS : CompletedPositiveSystem κ d F Λ)
    (hκ : κ ≤ d) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv
      (fun n => (relDeficit (fun n => d * ArithmeticFunction.vonMangoldt n) b n : ℂ)) <
        (1 / 2 : ℝ)) :
    κ = d ∧ (∀ n, n ≠ 0 → b n = d * ArithmeticFunction.vonMangoldt n) ∧
      ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * riemannZeta s ^ d := by
  set a : ℕ → ℝ := fun n => d * ArithmeticFunction.vonMangoldt n with hadef
  have ha : ∀ n, 0 ≤ a n := fun n => mul_nonneg (Nat.cast_nonneg d) ArithmeticFunction.vonMangoldt_nonneg
  obtain ⟨σE, hσEd, hσE⟩ := EReal.lt_iff_exists_real_btwn.mp hdef
  have hσE' : σE < 1 / 2 := by exact_mod_cast hσE
  set D : ℂ → ℂ := LSeries (fun n => (relDeficit a b n : ℂ)) with hDdef
  have hE : DifferentiableOn ℂ (fun s => (((b 1 - a 1 : ℝ)) : ℂ) - D s) {s : ℂ | σE < s.re} :=
    fun s hs => ((differentiableAt_const _).sub (LSeries_hasDerivAt (lt_trans hσEd
      (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt).differentiableWithinAt
  obtain ⟨hmass, hsplit⟩ := relMember_primeMass_split ha hb (abscissaOfAbsConv_zeta_pow_le_one d)
    habs hL (F₀ := fun w => riemannZeta w ^ d) (fun s hs => neg_logDeriv_zeta_pow_eq_LSeries d hs)
  obtain ⟨hκd, K, hK0, hFK⟩ := zetaPowDeformation_trivial hS hκ hmass hσE' hE hsplit
  refine ⟨hκd, fun n hn => ?_, K, hK0, hFK⟩
  -- `F = K ζ^d` makes the two Dirichlet series agree on `Re s > 1`
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLeq : ∀ s : ℂ, 1 < s.re → LSeries (fun n => (b n : ℂ)) s =
      LSeries (fun n => ((d * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    intro s hs
    have hev : F =ᶠ[𝓝 s] fun w => (K : ℂ) * riemannZeta w ^ d :=
      Filter.eventually_of_mem (hU.mem_nhds hs) fun w hw => hFK w hw
    rw [← hL s hs, ← neg_logDeriv_zeta_pow_eq_LSeries d hs, logDeriv_apply, hev.deriv_eq,
      hev.eq_of_nhds, ← logDeriv_apply, logDeriv_const_mul _ _ (by exact_mod_cast hK0)]
  have h1top : (1 : EReal) < ⊤ := by exact_mod_cast EReal.coe_lt_top 1
  have h := LSeries.eq_of_LSeries_eventually_eq (f := fun n => (b n : ℂ))
    (g := fun n => ((d * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (lt_of_le_of_lt habs h1top)
    (lt_of_le_of_lt (abscissaOfAbsConv_zeta_pow_le_one d) h1top)
    (Filter.eventually_atTop.mpr ⟨2, fun x hx => hLeq x (by simp only [Complex.ofReal_re]; linarith)⟩)
    hn
  exact_mod_cast h

end GaloisForLFunctions.BiarithmeticGaugeGeometry
