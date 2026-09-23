import GaloisForLFunctions.HTGeometry.RungePolePush
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnSum
import GaloisForLFunctions.HTGeometry.HardyDifferentialAlgebraicInterlacing

/-!
# The differentially algebraic approximation class of a domain

Runge approximation is assembled through one bookkeeping device: uniform approximability on a
compact set by members of a fixed ℂ-subspace of functions.  The subspace used here is the class of
functions analytic *and* differentially algebraic on `Ω`; it contains the polynomials and the
Cauchy kernels `(· − b)⁻¹` with `b ∉ Ω`, and is closed under sums and scalar multiples, which is all
the assembly needs.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set

noncomputable section

/-- Uniform approximability on `K` by members of `C`. -/
def ApproxOn (K : Set ℂ) (C : Set (ℂ → ℂ)) (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ g ∈ C, ∀ z ∈ K, ‖f z - g z‖ ≤ ε

theorem approxOn_of_mem {K : Set ℂ} {C : Set (ℂ → ℂ)} {f : ℂ → ℂ} (hf : f ∈ C) :
    ApproxOn K C f := by
  intro ε hε
  exact ⟨f, hf, fun z _ => by simp [hε.le]⟩

theorem approxOn_add {K : Set ℂ} {C : Set (ℂ → ℂ)}
    (hC : ∀ g₁ ∈ C, ∀ g₂ ∈ C, (fun z => g₁ z + g₂ z) ∈ C)
    {f₁ f₂ : ℂ → ℂ} (h₁ : ApproxOn K C f₁) (h₂ : ApproxOn K C f₂) :
    ApproxOn K C (fun z => f₁ z + f₂ z) := by
  intro ε hε
  obtain ⟨g₁, hg₁C, hg₁⟩ := h₁ (ε / 2) (by positivity)
  obtain ⟨g₂, hg₂C, hg₂⟩ := h₂ (ε / 2) (by positivity)
  refine ⟨fun z => g₁ z + g₂ z, hC g₁ hg₁C g₂ hg₂C, fun z hz => ?_⟩
  have hsplit : f₁ z + f₂ z - (g₁ z + g₂ z) = (f₁ z - g₁ z) + (f₂ z - g₂ z) := by ring
  rw [hsplit]
  have := norm_add_le (f₁ z - g₁ z) (f₂ z - g₂ z)
  have h1 := hg₁ z hz
  have h2 := hg₂ z hz
  linarith

theorem approxOn_smul {K : Set ℂ} {C : Set (ℂ → ℂ)}
    (hC : ∀ (c : ℂ), ∀ g ∈ C, (fun z => c * g z) ∈ C)
    (c : ℂ) {f : ℂ → ℂ} (h : ApproxOn K C f) :
    ApproxOn K C (fun z => c * f z) := by
  intro ε hε
  rcases eq_or_ne c 0 with rfl | hc
  · obtain ⟨g, hgC, _⟩ := h 1 one_pos
    refine ⟨fun z => (0 : ℂ) * g z, hC 0 g hgC, fun z _ => ?_⟩
    simp [hε.le]
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    obtain ⟨g, hgC, hg⟩ := h (ε / ‖c‖) (by positivity)
    refine ⟨fun z => c * g z, hC c g hgC, fun z hz => ?_⟩
    have hfac : c * f z - c * g z = c * (f z - g z) := by ring
    rw [hfac, norm_mul]
    have := hg z hz
    calc ‖c‖ * ‖f z - g z‖ ≤ ‖c‖ * (ε / ‖c‖) := by nlinarith
      _ = ε := by field_simp

theorem approxOn_finsetSum {K : Set ℂ} {C : Set (ℂ → ℂ)}
    (hC0 : (fun _ : ℂ => (0 : ℂ)) ∈ C)
    (hC : ∀ g₁ ∈ C, ∀ g₂ ∈ C, (fun z => g₁ z + g₂ z) ∈ C)
    {ι : Type*} (t : Finset ι) {f : ι → ℂ → ℂ}
    (h : ∀ i ∈ t, ApproxOn K C (f i)) :
    ApproxOn K C (fun z => ∑ i ∈ t, f i z) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using approxOn_of_mem hC0
  | @insert j t hj ih =>
      have hrest := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hj' := h j (Finset.mem_insert_self j t)
      have hsum := approxOn_add hC hj' hrest
      have hfun : (fun z => ∑ i ∈ insert j t, f i z)
          = fun z => f j z + ∑ i ∈ t, f i z := by
        funext z
        rw [Finset.sum_insert hj]
      rw [hfun]
      exact hsum

/-- Approximability is transitive through an intermediate uniform approximation. -/
theorem approxOn_of_approxOn {K : Set ℂ} {C : Set (ℂ → ℂ)} {f : ℂ → ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℂ → ℂ, ApproxOn K C h₀ ∧ ∀ z ∈ K, ‖f z - h₀ z‖ ≤ ε) :
    ApproxOn K C f := by
  intro ε hε
  obtain ⟨h₀, hh₀approx, hh₀⟩ := h (ε / 2) (by positivity)
  obtain ⟨g, hgC, hg⟩ := hh₀approx (ε / 2) (by positivity)
  refine ⟨g, hgC, fun z hz => ?_⟩
  have hsplit : f z - g z = (f z - h₀ z) + (h₀ z - g z) := by ring
  rw [hsplit]
  have := norm_add_le (f z - h₀ z) (h₀ z - g z)
  have h1 := hh₀ z hz
  have h2 := hg z hz
  linarith


/-! ## The differentially algebraic analytic class of a domain -/

/-- Functions analytic and differentially algebraic on `Ω`. -/
def RungeDA (Ω : Set ℂ) : Set (ℂ → ℂ) :=
  {G | AnalyticOnNhd ℂ G Ω ∧ DifferentiallyAlgebraicOn G Ω}

variable {Ω : Set ℂ}

theorem rungeDA_const (c : ℂ) : (fun _ : ℂ => c) ∈ RungeDA Ω :=
  ⟨fun _ _ => analyticAt_const, differentiallyAlgebraicOn_const Ω c⟩

theorem rungeDA_zero : (fun _ : ℂ => (0 : ℂ)) ∈ RungeDA Ω := rungeDA_const 0

theorem rungeDA_add (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    (hΩinf : Ω.Infinite) :
    ∀ g₁ ∈ RungeDA Ω, ∀ g₂ ∈ RungeDA Ω, (fun z => g₁ z + g₂ z) ∈ RungeDA Ω := by
  rintro g₁ ⟨ha₁, hd₁⟩ g₂ ⟨ha₂, hd₂⟩
  exact ⟨fun z hz => (ha₁ z hz).add (ha₂ z hz),
    differentiallyAlgebraicOn_add_differentialAlgebraicOnSum hΩo hΩc hΩne hΩinf ha₁ ha₂ hd₁ hd₂⟩

theorem rungeDA_smul (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    (hΩinf : Ω.Infinite) :
    ∀ (c : ℂ), ∀ g ∈ RungeDA Ω, (fun z => c * g z) ∈ RungeDA Ω := by
  rintro c g ⟨ha, hd⟩
  exact ⟨fun z hz => analyticAt_const.mul (ha z hz),
    differentiallyAlgebraicOn_const_mul hΩo hΩc hΩne hΩinf c ha hd⟩

theorem rungeDA_mul (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    (hΩinf : Ω.Infinite) :
    ∀ g₁ ∈ RungeDA Ω, ∀ g₂ ∈ RungeDA Ω, (fun z => g₁ z * g₂ z) ∈ RungeDA Ω := by
  rintro g₁ ⟨ha₁, hd₁⟩ g₂ ⟨ha₂, hd₂⟩
  exact ⟨fun z hz => (ha₁ z hz).mul (ha₂ z hz),
    differentiallyAlgebraicOn_mul hΩo hΩc hΩne hΩinf ha₁ ha₂ hd₁ hd₂⟩

theorem rungeDA_polynomial (B : Polynomial ℂ) : (fun z => B.eval z) ∈ RungeDA Ω :=
  ⟨fun z _ => (Complex.analyticOnNhd_univ_iff_differentiable.2 B.differentiable) z
    (Set.mem_univ z), differentiallyAlgebraicOn_polynomial Ω B⟩

theorem rungeDA_cauchyKernel {b : ℂ} (hb : b ∉ Ω) : (fun z => (z - b)⁻¹) ∈ RungeDA Ω := by
  have hne : ∀ z ∈ Ω, z - b ≠ 0 := by
    intro z hz
    exact sub_ne_zero.2 (fun hcon => hb (hcon ▸ hz))
  refine ⟨fun z hz => AnalyticAt.inv (analyticAt_id.sub analyticAt_const) (hne z hz), ?_⟩
  refine ⟨0, MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C b * MvPolynomial.X 1 - 1, ?_, ?_⟩
  · intro hzero
    have hev := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then b + 1 else 0)) hzero
    simp at hev
  · intro z hz
    have hval1 : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) (fun w => (w - b)⁻¹) z) :
        Fin 2 → ℂ) 1 = (z - b)⁻¹ := by
      rw [show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
      simp [iteratedDeriv_zero]
    have hval0 : (Fin.cons z (fun j : Fin 1 => iteratedDeriv (j : ℕ) (fun w => (w - b)⁻¹) z) :
        Fin 2 → ℂ) 0 = z := rfl
    simp only [map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_one, hval0, hval1]
    field_simp [hne z hz]
    norm_num

theorem rungeDA_cauchyKernel_pow (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    (hΩinf : Ω.Infinite) {b : ℂ} (hb : b ∉ Ω) (k : ℕ) :
    (fun z => ((z - b)⁻¹) ^ k) ∈ RungeDA Ω := by
  induction k with
  | zero => simpa using rungeDA_const (Ω := Ω) 1
  | succ k ih =>
      have := rungeDA_mul hΩo hΩc hΩne hΩinf _ (rungeDA_cauchyKernel hb) _ ih
      have hfun : (fun z => ((z - b)⁻¹) ^ (k + 1))
          = fun z => (z - b)⁻¹ * ((z - b)⁻¹) ^ k := by
        funext z
        ring
      rw [hfun]
      exact this

theorem rungeDA_polePushSum (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty)
    (hΩinf : Ω.Infinite) {a b : ℂ} (hb : b ∉ Ω) (N : ℕ) :
    (fun z => polePushSum a b N z) ∈ RungeDA Ω := by
  classical
  have hterm : ∀ n : ℕ, (fun z => (a - b) ^ n * ((z - b)⁻¹) ^ (n + 1)) ∈ RungeDA Ω := fun n =>
    rungeDA_smul hΩo hΩc hΩne hΩinf _ _ (rungeDA_cauchyKernel_pow hΩo hΩc hΩne hΩinf hb (n + 1))
  have hsum : ∀ (t : Finset ℕ),
      (fun z => ∑ n ∈ t, (a - b) ^ n * ((z - b)⁻¹) ^ (n + 1)) ∈ RungeDA Ω := by
    intro t
    induction t using Finset.induction with
    | empty => simpa using rungeDA_zero (Ω := Ω)
    | @insert j t hj ih =>
        have hfun : (fun z => ∑ n ∈ insert j t, (a - b) ^ n * ((z - b)⁻¹) ^ (n + 1))
            = fun z => (a - b) ^ j * ((z - b)⁻¹) ^ (j + 1)
              + ∑ n ∈ t, (a - b) ^ n * ((z - b)⁻¹) ^ (n + 1) := by
          funext z
          rw [Finset.sum_insert hj]
        rw [hfun]
        exact rungeDA_add hΩo hΩc hΩne hΩinf _ (hterm j) _ ih
  exact hsum (Finset.range N)

theorem rungeDA_infPushSum {a : ℂ} (N : ℕ) : (fun z => infPushSum a N z) ∈ RungeDA Ω := by
  classical
  have hpoly : (fun z : ℂ => infPushSum a N z)
      = fun z => (-∑ n ∈ Finset.range N,
          Polynomial.C ((a⁻¹) ^ (n + 1)) * Polynomial.X ^ n).eval z := by
    funext z
    rw [infPushSum]
    simp [Polynomial.eval_finsetSum]
    ring_nf
  rw [hpoly]
  exact rungeDA_polynomial _

end

end GaloisForLFunctions.HTGeometry
