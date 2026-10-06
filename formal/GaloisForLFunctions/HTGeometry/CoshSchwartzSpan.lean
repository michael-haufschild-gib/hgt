import GaloisForLFunctions.HTGeometry.SmoothDerivativeChain

/-!
# Schwartz functions of `cosh`

For `c ∈ ℝ` let `𝒜_c` be the complex span of the functions

`w ↦ cosh(w)^a sinh(w)^b χ(c cosh w)`,   `a, b ∈ ℕ`,   `χ` a Schwartz function on `ℝ`.

The chain rule gives

`(cosh^a sinh^b χ(c cosh))' = a cosh^{a-1} sinh^{b+1} χ(c cosh) + b cosh^{a+1} sinh^{b-1} χ(c cosh)
  + c cosh^a sinh^{b+1} χ'(c cosh)`,

so `𝒜_c` is closed under differentiation (`differentiable_and_deriv_mem_coshSchwartzSpan`): every
member is smooth and all its iterated derivatives lie in `𝒜_c`.  For `c ≠ 0` every member decays
faster than any exponential, `|f(w)| ≤ C_N e^{-N|w|}` (`exists_bound_of_mem_coshSchwartzSpan`):
`|cosh^a sinh^b| ≤ cosh^{a+b}` and `|χ(c cosh w)| ≤ S_k (|c| cosh w)^{-k}`.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `w ↦ cosh(w)^a sinh(w)^b χ(c cosh w)`. -/
def coshSchwartzTerm (c : ℝ) (a b : ℕ) (χ : SchwartzMap ℝ ℂ) (w : ℝ) : ℂ :=
  ((Real.cosh w ^ a * Real.sinh w ^ b : ℝ) : ℂ) * χ (c * Real.cosh w)

theorem hasDerivAt_coshSchwartzTerm (c : ℝ) (a b : ℕ) (χ : SchwartzMap ℝ ℂ) (w : ℝ) :
    HasDerivAt (coshSchwartzTerm c a b χ)
      ((a : ℂ) * coshSchwartzTerm c (a - 1) (b + 1) χ w +
        (b : ℂ) * coshSchwartzTerm c (a + 1) (b - 1) χ w +
        (c : ℂ) * coshSchwartzTerm c a (b + 1) (SchwartzMap.derivCLM ℝ ℂ χ) w) w := by
  have hp : HasDerivAt (fun w : ℝ => Real.cosh w ^ a * Real.sinh w ^ b)
      ((a : ℝ) * Real.cosh w ^ (a - 1) * Real.sinh w * Real.sinh w ^ b +
        Real.cosh w ^ a * ((b : ℝ) * Real.sinh w ^ (b - 1) * Real.cosh w)) w :=
    ((Real.hasDerivAt_cosh w).pow a).mul ((Real.hasDerivAt_sinh w).pow b)
  have hχ : HasDerivAt (fun w : ℝ => χ (c * Real.cosh w))
      ((c * Real.sinh w) • deriv χ (c * Real.cosh w)) w :=
    (χ.hasDerivAt (c * Real.cosh w)).scomp w ((Real.hasDerivAt_cosh w).const_mul c)
  refine (hp.ofReal_comp.mul hχ).congr_deriv ?_
  simp only [coshSchwartzTerm, SchwartzMap.derivCLM_apply, Complex.real_smul]
  push_cast
  ring

/-- The span `𝒜_c` of the functions `cosh^a sinh^b χ(c cosh)`. -/
def coshSchwartzSpan (c : ℝ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range fun p : ℕ × ℕ × SchwartzMap ℝ ℂ => coshSchwartzTerm c p.1 p.2.1 p.2.2)

theorem coshSchwartzTerm_mem (c : ℝ) (a b : ℕ) (χ : SchwartzMap ℝ ℂ) :
    coshSchwartzTerm c a b χ ∈ coshSchwartzSpan c :=
  Submodule.subset_span ⟨(a, b, χ), rfl⟩

/-- **`𝒜_c` is closed under differentiation.** -/
theorem differentiable_and_deriv_mem_coshSchwartzSpan {c : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ coshSchwartzSpan c) : Differentiable ℝ f ∧ deriv f ∈ coshSchwartzSpan c := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨a, b, χ⟩, rfl⟩ := hx
      refine ⟨fun w => (hasDerivAt_coshSchwartzTerm c a b χ w).differentiableAt, ?_⟩
      have hd : deriv (coshSchwartzTerm c a b χ) =
          (a : ℂ) • coshSchwartzTerm c (a - 1) (b + 1) χ + (b : ℂ) • coshSchwartzTerm c (a + 1) (b - 1) χ +
            (c : ℂ) • coshSchwartzTerm c a (b + 1) (SchwartzMap.derivCLM ℝ ℂ χ) := by
        funext w
        rw [(hasDerivAt_coshSchwartzTerm c a b χ w).deriv]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hd]
      exact Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (coshSchwartzTerm_mem c _ _ _))
        (Submodule.smul_mem _ _ (coshSchwartzTerm_mem c _ _ _)))
        (Submodule.smul_mem _ _ (coshSchwartzTerm_mem c _ _ _))
  | zero =>
      refine ⟨differentiable_const 0, ?_⟩
      have : deriv (0 : ℝ → ℂ) = 0 := funext fun w => deriv_const w (0 : ℂ)
      rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      have : deriv (x + y) = deriv x + deriv y := funext fun w => deriv_add (hx.1 w) (hy.1 w)
      rw [this]; exact Submodule.add_mem _ hx.2 hy.2
  | smul k x _ hx =>
      refine ⟨hx.1.const_smul k, ?_⟩
      have : deriv (k • x) = k • deriv x := funext fun w => deriv_const_smul k (hx.1 w)
      rw [this]; exact Submodule.smul_mem _ k hx.2

theorem iterate_deriv_mem_coshSchwartzSpan {c : ℝ} {f : ℝ → ℂ} (hf : f ∈ coshSchwartzSpan c)
    (m : ℕ) : deriv^[m] f ∈ coshSchwartzSpan c := by
  induction m with
  | zero => exact hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact (differentiable_and_deriv_mem_coshSchwartzSpan ih).2

theorem hasDerivAt_iterate_deriv_of_mem_coshSchwartzSpan {c : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ coshSchwartzSpan c) (m : ℕ) (w : ℝ) :
    HasDerivAt (deriv^[m] f) (deriv^[m + 1] f w) w := by
  rw [Function.iterate_succ_apply']
  exact ((differentiable_and_deriv_mem_coshSchwartzSpan
    (iterate_deriv_mem_coshSchwartzSpan hf m)).1 w).hasDerivAt

/-- Members of `𝒜_c` are smooth. -/
theorem contDiff_of_mem_coshSchwartzSpan {c : ℝ} {f : ℝ → ℂ} (hf : f ∈ coshSchwartzSpan c) (n : ℕ) :
    ContDiff ℝ n f := by
  simpa using contDiff_nat_of_hasDerivAt_chain
    (hasDerivAt_iterate_deriv_of_mem_coshSchwartzSpan hf) n 0

/-- Iterated derivatives of members of `𝒜_c` lie in `𝒜_c`. -/
theorem iteratedDeriv_mem_coshSchwartzSpan {c : ℝ} {f : ℝ → ℂ} (hf : f ∈ coshSchwartzSpan c)
    (n : ℕ) : iteratedDeriv n f ∈ coshSchwartzSpan c := by
  have h := iteratedDeriv_eq_of_hasDerivAt_chain
    (hasDerivAt_iterate_deriv_of_mem_coshSchwartzSpan hf) 0 n
  simp only [Function.iterate_zero, id_eq, zero_add] at h
  rw [h]; exact iterate_deriv_mem_coshSchwartzSpan hf n

theorem exp_abs_le_two_mul_cosh (w : ℝ) : Real.exp |w| ≤ 2 * Real.cosh w := by
  rw [Real.cosh_eq]
  rcases le_total 0 w with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-w)]
  · rw [abs_of_nonpos h]; linarith [Real.exp_pos w]

theorem norm_coshSchwartzTerm_le {c : ℝ} (hc : c ≠ 0) (a b : ℕ) (χ : SchwartzMap ℝ ℂ) (N : ℕ)
    (w : ℝ) :
    ‖coshSchwartzTerm c a b χ w‖ ≤
      2 ^ N * (SchwartzMap.seminorm ℝ (N + a + b) 0 χ / |c| ^ (N + a + b)) * Real.exp (-(N * |w|)) := by
  set k := N + a + b
  set S := SchwartzMap.seminorm ℝ k 0 χ
  have hch : 1 ≤ Real.cosh w := Real.one_le_cosh w
  have hch0 : 0 < Real.cosh w := by linarith
  have hc0 : 0 < |c| := abs_pos.2 hc
  have hS := SchwartzMap.norm_pow_mul_le_seminorm ℝ χ k (c * Real.cosh w)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hch0, mul_pow] at hS
  have hsinh : |Real.sinh w| ≤ Real.cosh w := by
    rw [abs_le]; constructor <;> nlinarith [Real.cosh_sq w, Real.sinh_sq w, Real.cosh_pos w,
      sq_nonneg (Real.cosh w + Real.sinh w), sq_nonneg (Real.cosh w - Real.sinh w)]
  have hpb : |Real.cosh w ^ a * Real.sinh w ^ b| ≤ Real.cosh w ^ (a + b) := by
    rw [abs_mul, abs_pow, abs_pow, abs_of_pos hch0, pow_add]
    gcongr
  have hχ : ‖χ (c * Real.cosh w)‖ ≤ S / (|c| ^ k * Real.cosh w ^ k) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hexp : Real.cosh w ^ N * Real.exp (-(N * |w|)) ≥ 1 / 2 ^ N := by
    have h1 := exp_abs_le_two_mul_cosh w
    have h2 : Real.exp |w| ^ N * Real.exp (-(N * |w|)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
    have h3 : Real.exp |w| ^ N ≤ 2 ^ N * Real.cosh w ^ N := by
      rw [← mul_pow]; gcongr
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (-(N * |w|))]
  unfold coshSchwartzTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |Real.cosh w ^ a * Real.sinh w ^ b| * ‖χ (c * Real.cosh w)‖
      ≤ Real.cosh w ^ (a + b) * (S / (|c| ^ k * Real.cosh w ^ k)) := by gcongr
    _ = S / |c| ^ k / Real.cosh w ^ N := by
        rw [show k = N + (a + b) by omega, pow_add]; field_simp; ring
    _ ≤ 2 ^ N * (S / |c| ^ k) * Real.exp (-(N * |w|)) := by
        have hS0 : 0 ≤ S / |c| ^ k := by positivity
        rw [div_le_iff₀ (by positivity)]
        calc S / |c| ^ k = S / |c| ^ k * 1 := (mul_one _).symm
          _ ≤ S / |c| ^ k * (2 ^ N * (Real.cosh w ^ N * Real.exp (-(N * |w|)))) := by
              gcongr
              rw [ge_iff_le, div_le_iff₀ (by positivity)] at hexp
              linarith
          _ = _ := by ring

/-- **Super-exponential decay**: for `c ≠ 0` every member of `𝒜_c` satisfies
`|f(w)| ≤ C_N e^{-N|w|}` for every `N`. -/
theorem exists_bound_of_mem_coshSchwartzSpan {c : ℝ} (hc : c ≠ 0) {f : ℝ → ℂ}
    (hf : f ∈ coshSchwartzSpan c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖f w‖ ≤ C * Real.exp (-(N * |w|)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨a, b, χ⟩, rfl⟩ := hx
      exact ⟨_, by positivity, norm_coshSchwartzTerm_le hc a b χ N⟩
  | zero => exact ⟨0, le_rfl, fun w => by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨C₁, hC₁, h₁⟩ := hx
      obtain ⟨C₂, hC₂, h₂⟩ := hy
      refine ⟨C₁ + C₂, by positivity, fun w => ?_⟩
      calc ‖(x + y) w‖ ≤ ‖x w‖ + ‖y w‖ := norm_add_le _ _
        _ ≤ C₁ * Real.exp (-(N * |w|)) + C₂ * Real.exp (-(N * |w|)) := add_le_add (h₁ w) (h₂ w)
        _ = _ := by ring
  | smul k x _ hx =>
      obtain ⟨C, hC, h⟩ := hx
      refine ⟨‖k‖ * C, by positivity, fun w => ?_⟩
      rw [Pi.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (h w) (norm_nonneg k)

/-- Every iterated derivative of a member of `𝒜_c`, `c ≠ 0`, decays super-exponentially. -/
theorem exists_bound_iteratedDeriv_of_mem_coshSchwartzSpan {c : ℝ} (hc : c ≠ 0) {f : ℝ → ℂ}
    (hf : f ∈ coshSchwartzSpan c) (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖iteratedDeriv n f w‖ ≤ C * Real.exp (-(N * |w|)) :=
  exists_bound_of_mem_coshSchwartzSpan hc (iteratedDeriv_mem_coshSchwartzSpan hf n) N

end

end GaloisForLFunctions.HTGeometry
