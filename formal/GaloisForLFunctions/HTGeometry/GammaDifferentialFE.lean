import Mathlib
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# The differentiated functional equation of Γ

Differentiating `Γ(s+1) = s·Γ(s)` (`Complex.Gamma_add_one`) `k` times via the Leibniz rule — the extra
factor `s` has vanishing derivatives beyond the first — gives the recurrence for the iterated
derivatives of Γ:

`Γ⁽ᵏ⁾(s+1) = s·Γ⁽ᵏ⁾(s) + k·Γ⁽ᵏ⁻¹⁾(s)`   (`iteratedDeriv_Gamma_add_one`).

This is the machinery the differential rungs of `Hypertranscendental Γ` (orders `≥ 1`) rest on: it is how
the functional equation enters the *differential* structure, not just the value structure.  Supporting
lemma `contDiffAt_Gamma`: Γ is `C^∞` at every point off `−ℕ` (as the reciprocal of the entire,
locally-nonvanishing `1/Γ`).
-/

open Complex Filter Topology Finset

namespace GaloisForLFunctions

/-- **Local continuity of an iterated derivative.**  If `f` is `ContDiffAt ℂ i` at `x`, then
`iteratedDeriv i f` is continuous at `x` — the `ContDiffAt` local analogue of
`ContDiff.continuous_iteratedDeriv`, via the iterated Fréchet derivative and the continuous evaluation
of a continuous multilinear map. -/
theorem continuousAt_iteratedDeriv_of_contDiffAt {f : ℂ → ℂ} {x : ℂ} {i : ℕ}
    (h : ContDiffAt ℂ i f x) : ContinuousAt (iteratedDeriv i f) x := by
  have hF : ContinuousAt (iteratedFDeriv ℂ i f) x := h.continuousAt_iteratedFDeriv le_rfl
  have happ : Continuous fun T : ContinuousMultilinearMap ℂ (fun _ : Fin i => ℂ) ℂ =>
      T (fun _ => 1) :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin i => ℂ) ℂ (fun _ => 1)).continuous
  have hc : ContinuousAt (fun y => (iteratedFDeriv ℂ i f y) (fun _ => 1)) x :=
    happ.continuousAt.comp hF
  have hfun :
      iteratedDeriv i f = fun y => (iteratedFDeriv ℂ i f y) (fun _ => 1) := by
    funext y
    rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hfun]
  exact hc

/-- **The `m`-th derivative of a simple pole.**  `d^m/ds^m (s+c)⁻¹ = (−1)^m·m!·(s+c)^{−(m+1)}` at any
`x` with `x+c ≠ 0`.  This is the Laurent structure of `(s+c)⁻¹` that the general derivative-residue of
Γ needs (`Γ = [analytic]/(s+k)`, so `Γ⁽ʲ⁾` is a Leibniz sum against these). -/
theorem iteratedDeriv_inv_add_const (c : ℂ) (m : ℕ) (x : ℂ) (hx : x + c ≠ 0) :
    iteratedDeriv m (fun s => (s + c)⁻¹) x
      = (-1) ^ m * (m.factorial : ℂ) * ((x + c) ^ (m + 1))⁻¹ := by
  induction m generalizing x with
  | zero => simp
  | succ n ih =>
    have hev : ∀ᶠ y in 𝓝 x, y + c ≠ 0 :=
      (continuousAt_id.add continuousAt_const).eventually_ne hx
    have hEq : iteratedDeriv n (fun s => (s + c)⁻¹)
        =ᶠ[𝓝 x] fun y => (-1) ^ n * (n.factorial : ℂ) * ((y + c) ^ (n + 1))⁻¹ := by
      filter_upwards [hev] with y hy; exact ih y hy
    have hp : HasDerivAt (fun y : ℂ => (y + c) ^ (n + 1)) ((↑(n + 1)) * (x + c) ^ n) x := by
      have hfun :
          (fun y : ℂ => (y + c) ^ (n + 1)) = (fun y : ℂ => y + c) ^ (n + 1) := by
        funext y
        rfl
      rw [hfun]
      have hbase : (fun y : ℂ => y + c) = fun y => id y + c := by
        funext y
        rfl
      rw [hbase]
      simpa only [id_eq, Nat.add_sub_cancel, mul_one] using
        ((hasDerivAt_id x).add_const c).pow (n + 1)
    have hinv : HasDerivAt (fun y : ℂ => ((y + c) ^ (n + 1))⁻¹)
        (-((↑(n + 1)) * (x + c) ^ n) / ((x + c) ^ (n + 1)) ^ 2) x :=
      hp.inv (pow_ne_zero (n + 1) hx)
    have hfull := hinv.const_mul ((-1) ^ n * (n.factorial : ℂ))
    rw [iteratedDeriv_succ]
    rw [hEq.deriv_eq]
    rw [hfull.deriv, Nat.factorial_succ, pow_succ (-1 : ℂ) n]
    push_cast; field_simp; ring

/-- **Finite unwinding of the functional equation.**  Iterating `Γ(s+1) = s·Γ(s)` gives
`Γ(s)·∏_{j=0}^{k}(s+j) = Γ(s+k+1)`, valid whenever none of `s, s+1, …, s+k` is a pole.  This exhibits
the pole of Γ at `−k` as the reciprocal of the vanishing product `∏(s+j)`, and is the starting point
for the residue `(s+k)·Γ(s) → (−1)^k/k!`. -/
theorem gamma_prod (k : ℕ) (s : ℂ) (hs : ∀ j : ℕ, j ≤ k → s + (j : ℂ) ≠ 0) :
    Complex.Gamma s * ∏ j ∈ Finset.range (k + 1), (s + (j : ℂ)) = Complex.Gamma (s + (k + 1 : ℕ)) := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.prod_singleton, Nat.cast_zero, add_zero,
      Nat.cast_one]
    rw [mul_comm]
    exact (Complex.Gamma_add_one s (by simpa using hs 0 le_rfl)).symm
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih (fun j hj => hs j (by omega))]
    have hne : s + ((n : ℂ) + 1) ≠ 0 := by
      have h := hs (n + 1) le_rfl; rwa [Nat.cast_add, Nat.cast_one] at h
    have harg : s + ((n : ℂ) + 1) + 1 = s + ((n + 1 + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [Nat.cast_add, Nat.cast_one, mul_comm, ← Complex.Gamma_add_one _ hne, harg]

/-- **Γ is `C^∞` off the poles.**  At any `x` with `x ∉ −ℕ`, Γ is `ContDiffAt` of every order: it is the
reciprocal of the entire function `1/Γ`, which is nonzero at `x`. -/
theorem contDiffAt_Gamma (x : ℂ) (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) (n : ℕ) :
    ContDiffAt ℂ n Complex.Gamma x := by
  have hinv : AnalyticAt ℂ (fun s => (Complex.Gamma s)⁻¹) x :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ) x
      (Set.mem_univ x)
  have hne : (fun s => (Complex.Gamma s)⁻¹) x ≠ 0 := inv_ne_zero (Complex.Gamma_ne_zero hx)
  have hΓ : AnalyticAt ℂ (fun s => ((Complex.Gamma s)⁻¹)⁻¹) x := hinv.inv hne
  have heq : (fun s => ((Complex.Gamma s)⁻¹)⁻¹) = Complex.Gamma := by funext s; rw [inv_inv]
  rw [heq] at hΓ
  exact hΓ.contDiffAt

/-- The iterated derivatives of the identity `fun s => s` vanish beyond order one. -/
private theorem iteratedDeriv_id_add_two (i : ℕ) (x : ℂ) :
    iteratedDeriv (i + 2) (id : ℂ → ℂ) x = 0 := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']; simp

/-- **The differentiated functional equation of Γ.**  For `x ∉ −ℕ` and every order `k`,
`Γ⁽ᵏ⁾(x+1) = x·Γ⁽ᵏ⁾(x) + k·Γ⁽ᵏ⁻¹⁾(x)`.  Obtained by differentiating `Γ(s+1) = s·Γ(s)` `k` times
(Leibniz; only the order-`0` and order-`1` derivatives of the factor `s` survive). -/
theorem iteratedDeriv_Gamma_add_one (k : ℕ) (x : ℂ) (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    iteratedDeriv k Complex.Gamma (x + 1)
      = x * iteratedDeriv k Complex.Gamma x + k * iteratedDeriv (k - 1) Complex.Gamma x := by
  have hx0 : x ≠ 0 := by simpa using hx 0
  have hshift : iteratedDeriv k Complex.Gamma (x + 1)
      = iteratedDeriv k (fun s => Complex.Gamma (s + 1)) x :=
    (congrFun (iteratedDeriv_comp_add_const k Complex.Gamma 1) x).symm
  rw [hshift]
  have hEq : (fun s => Complex.Gamma (s + 1)) =ᶠ[𝓝 x] id * Complex.Gamma := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with s hs
    show Complex.Gamma (s + 1) = s * Complex.Gamma s
    exact Complex.Gamma_add_one s hs
  rw [hEq.iteratedDeriv_eq,
    iteratedDeriv_mul (𝕜 := ℂ) contDiffAt_id (contDiffAt_Gamma x hx k)]
  rcases k with _ | n
  · simp
  · rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ' _ n,
      Finset.sum_eq_zero (fun i _ => by rw [iteratedDeriv_id_add_two i x]; simp)]
    have hd1 : iteratedDeriv 1 (id : ℂ → ℂ) x = 1 := by rw [iteratedDeriv_one]; simp
    simp only [Nat.choose_zero_right, Nat.choose_one_right, iteratedDeriv_zero, id_eq, hd1,
      zero_add, Nat.succ_sub_one, Nat.cast_succ]
    push_cast
    ring

/-- **The residue of Γ at `0` is `1`.**  `s·Γ(s) = Γ(s+1) → Γ(1) = 1` as `s → 0`. -/
theorem gamma_residue_zero :
    Tendsto (fun s : ℂ => s * Complex.Gamma s) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have h1ne : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m h; have hr := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hg : ContinuousAt Complex.Gamma 1 := (Complex.differentiableAt_Gamma 1 h1ne).continuousAt
  have hf : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h0 : Tendsto (fun s : ℂ => s + 1) (𝓝 (0 : ℂ)) (𝓝 (0 + 1)) :=
      (continuous_id.add continuous_const).continuousAt
    rw [zero_add] at h0; exact h0.mono_left nhdsWithin_le_nhds
  have hcomp := hg.tendsto.comp hf
  rw [Complex.Gamma_one] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact Complex.Gamma_add_one s (by simpa using hs)

/-- **The residue of Γ at every pole `−k` is `(−1)^k/k!`.**  `(s+k)·Γ(s) → (−1)^k/k!` as `s → −k`,
proved by induction on `k`: the base case is `gamma_residue_zero`, and the step divides by `s` after
shifting `s ↦ s+1` (which sends the pole `−(k+1)` to `−k`).  This is the leading Laurent datum of Γ at
its poles — the factorial growth `1/|r_k| = k!` is what a pole-counting argument for the higher
(differential) rungs of `Hypertranscendental Γ` exploits. -/
theorem gamma_residue (k : ℕ) :
    Tendsto (fun s : ℂ => (s + (k : ℂ)) * Complex.Gamma s) (𝓝[≠] (-(k : ℂ)))
      (𝓝 ((-1) ^ k / (k.factorial : ℂ))) := by
  induction k with
  | zero => simpa using gamma_residue_zero
  | succ n ih =>
    have hshift : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h0 : Tendsto (fun s : ℂ => s + 1) (𝓝 (-((n + 1 : ℕ) : ℂ)))
            (𝓝 (-((n + 1 : ℕ) : ℂ) + 1)) := (continuous_id.add continuous_const).continuousAt
        have he : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
        rw [he] at h0; exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
        intro h; apply hs; push_cast at h ⊢; linear_combination h
    have hden : Tendsto (fun s : ℂ => s) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝 (-((n + 1 : ℕ) : ℂ))) :=
      continuousWithinAt_id
    have hne : (-((n + 1 : ℕ) : ℂ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
    have hcomp := (ih.comp hshift).div hden hne
    have hval : (-1 : ℂ) ^ n / (n.factorial : ℂ) / (-((n + 1 : ℕ) : ℂ))
        = (-1) ^ (n + 1) / ((n + 1).factorial : ℂ) := by
      have hnf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [Nat.factorial_succ]; push_cast; field_simp; ring
    rw [hval] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (-((n + 1 : ℕ) : ℂ)) (show (0 : ℝ) < 1 / 2 by norm_num))] with s hsb
    have hs0 : s ≠ 0 := by
      rw [Complex.dist_eq] at hsb
      intro h; rw [h] at hsb; simp only [zero_sub, norm_neg, Complex.norm_natCast] at hsb
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) :=
        by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
      linarith
    simp only [Pi.div_apply, Function.comp_apply]
    rw [Complex.Gamma_add_one s hs0]
    push_cast; field_simp; ring

/-- **Γ′ is continuous off the poles.**  For `x ∉ −ℕ`, `deriv Γ` is continuous at `x` (Γ is `C²`
there, so its derivative is `C¹`, via the Fréchet derivative). -/
theorem contDiffAt_deriv_Gamma (x : ℂ) (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    ContinuousAt (deriv Complex.Gamma) x := by
  have hfd : ContinuousAt (fderiv ℂ Complex.Gamma) x :=
    (contDiffAt_Gamma x hx 2).continuousAt_fderiv (by norm_num)
  have h1 : ContinuousAt (fun y => (fderiv ℂ Complex.Gamma y) 1) x :=
    hfd.clm_apply continuousAt_const
  simpa only [fderiv_apply_one_eq_deriv] using h1

/-- **The digamma function is continuous off the poles.**  For `x ∉ −ℕ`, `ψ = Γ′/Γ` is continuous at
`x` (numerator and denominator continuous, denominator nonzero). -/
theorem continuousAt_digamma (x : ℂ) (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) :
    ContinuousAt Complex.digamma x := by
  have hg : ContinuousAt Complex.Gamma x := (contDiffAt_Gamma x hx 1).continuousAt
  have := (contDiffAt_deriv_Gamma x hx).div hg (Complex.Gamma_ne_zero hx)
  rw [Complex.digamma_def]
  change ContinuousAt (deriv Complex.Gamma / Complex.Gamma) x
  exact this

/-- **Γ′ is `C^n` off the poles.**  `deriv Γ` is `ContDiffAt ℂ n` at every `x ∉ −ℕ` (Γ is `C^{n+1}`
there; the derivative is `C^n`, via the Fréchet derivative). -/
theorem contDiffAt_deriv_Gamma_n (x : ℂ) (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) (n : ℕ) :
    ContDiffAt ℂ n (deriv Complex.Gamma) x := by
  have hfd : ContDiffAt ℂ n (fderiv ℂ Complex.Gamma) x :=
    (contDiffAt_Gamma x hx (n + 1)).fderiv_right (by norm_cast)
  have h1 : ContDiffAt ℂ n (fun y => (fderiv ℂ Complex.Gamma y) 1) x := hfd.clm_apply contDiffAt_const
  simpa only [fderiv_apply_one_eq_deriv] using h1

/-- **The digamma function is `C^n` off the poles.**  `ψ = Γ′/Γ` is `ContDiffAt ℂ n` at every `x ∉ −ℕ`
(quotient of the `C^n` functions `Γ′` and `Γ`, denominator nonzero).  This is the smoothness the
polygamma residues `(s+k)^{i+1}·ψ⁽ⁱ⁾(s) → (−1)^i i!` are built on. -/
theorem contDiffAt_digamma_n (x : ℂ) (hx : ∀ m : ℕ, x ≠ -(m : ℂ)) (n : ℕ) :
    ContDiffAt ℂ n Complex.digamma x := by
  have h := (contDiffAt_deriv_Gamma_n x hx n).div (contDiffAt_Gamma x hx n) (Complex.Gamma_ne_zero hx)
  rw [Complex.digamma_def]
  change ContDiffAt ℂ n (deriv Complex.Gamma / Complex.Gamma) x
  exact h

private theorem ball_avoids {k : ℕ} {s : ℂ} (hsb : s ∈ Metric.ball (-(k:ℂ)) (1/2)) (hsne : s ≠ -(k:ℂ)) :
    ∀ m : ℕ, s ≠ -(m:ℂ) := by
  intro m hm
  rcases eq_or_ne m k with rfl | hmk
  · exact hsne hm
  · rw [Metric.mem_ball, Complex.dist_eq, hm] at hsb
    have : (1:ℝ) ≤ ‖(-(m:ℂ)) - (-(k:ℂ))‖ := by
      rw [show (-(m:ℂ)) - (-(k:ℂ)) = (((k:ℤ) - m : ℤ):ℂ) by push_cast; ring, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs (by omega : ((k:ℤ) - m) ≠ 0)
    linarith
theorem digamma_residue (k : ℕ) :
    Tendsto (fun s : ℂ => (s + (k:ℂ)) * Complex.digamma s) (𝓝[≠] (-(k:ℂ))) (𝓝 (-1)) := by
  have h1ne : ∀ m : ℕ, (1:ℂ) ≠ -(m:ℂ) := by
    intro m h; have hr := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) m]
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero, neg_zero]
    have hf : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] (0:ℂ)) (𝓝 1) := by
      have h0 : Tendsto (fun s : ℂ => s + 1) (𝓝 (0:ℂ)) (𝓝 (0 + 1)) :=
        (continuous_id.add continuous_const).continuousAt
      rw [zero_add] at h0; exact h0.mono_left nhdsWithin_le_nhds
    have hcont := (continuousAt_digamma 1 h1ne).tendsto.comp hf
    have hmul : Tendsto (fun s : ℂ => s * Complex.digamma (s + 1)) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
      have := (tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0:ℂ)))).mul hcont
      simpa using this
    have hsub : Tendsto (fun s : ℂ => s * Complex.digamma (s + 1) - 1) (𝓝[≠] (0:ℂ)) (𝓝 (-1)) := by
      have := hmul.sub (tendsto_const_nhds (α := ℂ) (x := (1:ℂ)) (f := 𝓝[≠] (0:ℂ)))
      simpa using this
    refine hsub.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
      with s hsb hsne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
    have hpole : ∀ m : ℕ, s ≠ -(m:ℂ) := by
      intro m hm
      rcases eq_or_ne m 0 with rfl | hmk
      · simp only [Nat.cast_zero, neg_zero] at hm; exact hsne hm
      · rw [Complex.dist_eq, hm, sub_zero, norm_neg, Complex.norm_natCast] at hsb
        have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmk
        linarith
    have hs0 : s ≠ 0 := by simpa using hpole 0
    rw [Complex.digamma_apply_add_one s hpole]; field_simp; ring
  | succ n ih =>
    have hshift : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h0 : Tendsto (fun s : ℂ => s + 1) (𝓝 (-((n + 1 : ℕ) : ℂ)))
            (𝓝 (-((n + 1 : ℕ) : ℂ) + 1)) := (continuous_id.add continuous_const).continuousAt
        have he : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
        rw [he] at h0; exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
        intro h; apply hs; push_cast at h ⊢; linear_combination h
    have hnum := ih.comp hshift
    have hfrac : Tendsto (fun s : ℂ => (s + ((n + 1 : ℕ) : ℂ)) / s) (𝓝[≠] (-((n + 1 : ℕ) : ℂ)))
        (𝓝 0) := by
      have hd : Tendsto (fun s : ℂ => s) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝 (-((n + 1 : ℕ) : ℂ))) :=
        continuousWithinAt_id
      have hnz : Tendsto (fun s : ℂ => s + ((n + 1 : ℕ) : ℂ)) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝 0) := by
        have : Tendsto (fun s : ℂ => s + ((n + 1 : ℕ) : ℂ)) (𝓝 (-((n + 1 : ℕ) : ℂ)))
            (𝓝 (-((n + 1 : ℕ) : ℂ) + ((n + 1 : ℕ) : ℂ))) := (continuous_id.add continuous_const).continuousAt
        rw [neg_add_cancel] at this; exact this.mono_left nhdsWithin_le_nhds
      have hne : (-((n + 1 : ℕ) : ℂ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
      have := hnz.div hd hne
      have hfun :
          (fun s : ℂ => (s + ((n + 1 : ℕ) : ℂ)) / s) =
            (fun s : ℂ => s + ((n + 1 : ℕ) : ℂ)) / fun s : ℂ => s := by
        funext s
        rfl
      rw [hfun]
      simpa only [zero_div] using this
    have hsub := hnum.sub hfrac
    rw [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (-((n + 1 : ℕ) : ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
      with s hsb hsne
    have hpole := ball_avoids hsb hsne
    have hs0 : s ≠ 0 := by simpa using hpole 0
    have hfe : Complex.digamma s = Complex.digamma (s + 1) - s⁻¹ := by
      rw [Complex.digamma_apply_add_one s hpole]; ring
    simp only [Function.comp_apply]
    rw [hfe]; push_cast; field_simp; ring

/-- **The residue of Γ′ at `−k`.**  `(s+k)²·Γ′(s) → −(−1)^k/k!`, the leading Laurent datum of the
first derivative: it is the product `[(s+k)·ψ(s)]·[(s+k)·Γ(s)] → (−1)·((−1)^k/k!)`, since
`Γ′ = ψ·Γ`.  (Higher derivatives follow by the polygamma analogues.) -/
theorem gamma_deriv_residue (k : ℕ) :
    Tendsto (fun s : ℂ => (s + (k : ℂ)) ^ 2 * deriv Complex.Gamma s) (𝓝[≠] (-(k : ℂ)))
      (𝓝 (-((-1) ^ k / (k.factorial : ℂ)))) := by
  have hmul := (digamma_residue k).mul (gamma_residue k)
  rw [show (-1 : ℂ) * ((-1) ^ k / (k.factorial : ℂ)) = -((-1) ^ k / (k.factorial : ℂ)) by ring] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (Metric.ball_mem_nhds (-(k : ℂ)) (show (0 : ℝ) < 1 / 2 by norm_num)), self_mem_nhdsWithin]
    with s hsb hsne
  have hpole := ball_avoids hsb hsne
  have hΓ0 : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hpole
  have hderiv : deriv Complex.Gamma s = Complex.digamma s * Complex.Gamma s := by
    rw [Complex.digamma_def, logDeriv_apply, div_mul_cancel₀ _ hΓ0]
  rw [hderiv]; ring

/-- **The analytic extension of `(s+k)·Γ(s)` is `C^n` at the pole.**  `G̃(s) = Γ(s+k+1)/∏_{j<k}(s+j)`
is `ContDiffAt ℂ n` at `−k`: the numerator `Γ(·+k+1)` is smooth there (`−k+k+1 = 1 ∉ −ℕ`) and the
denominator is a polynomial that is nonzero at `−k`.  This is the removable-singularity–free analytic
extension of the pole of Γ. -/
theorem contDiffAt_gammaExtension (k n : ℕ) :
    ContDiffAt ℂ n
      (fun s : ℂ => Complex.Gamma (s + ((k + 1 : ℕ) : ℂ)) / ∏ j ∈ Finset.range k, (s + (j : ℂ)))
      (-(k : ℂ)) := by
  have h1ne : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
    intro m h; have hr := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hpt : (-(k : ℂ)) + ((k + 1 : ℕ) : ℂ) = 1 := by push_cast; ring
  have hg : ContDiffAt ℂ n Complex.Gamma ((-(k : ℂ)) + ((k + 1 : ℕ) : ℂ)) := by
    rw [hpt]; exact contDiffAt_Gamma 1 h1ne n
  have hnum : ContDiffAt ℂ n (fun s : ℂ => Complex.Gamma (s + ((k + 1 : ℕ) : ℂ))) (-(k : ℂ)) :=
    hg.comp (-(k : ℂ)) (by fun_prop)
  have hden : ContDiffAt ℂ n (fun s : ℂ => ∏ j ∈ Finset.range k, (s + (j : ℂ))) (-(k : ℂ)) := by
    fun_prop
  have hne : (∏ j ∈ Finset.range k, ((-(k : ℂ)) + (j : ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj; rw [Finset.mem_range] at hj
    intro h; have hjk : (j : ℂ) = (k : ℂ) := by linear_combination h
    exact absurd (by exact_mod_cast hjk : j = k) (by omega)
  exact hnum.div hden hne

/-- **The Gamma pole factorizes near `−k`.**  For `s` in a punctured neighbourhood of `−k`,
`Γ(s) = [Γ(s+k+1)/∏_{j<k}(s+j)] · (s+k)⁻¹` — the analytic extension `G̃` times the simple pole.  From
`gamma_prod`.  With `contDiffAt_gammaExtension` and `iteratedDeriv_inv_add_const`, differentiating this
`j` times (Leibniz) and taking `s → −k` gives `(s+k)^{j+1}·Γ⁽ʲ⁾(s) → (−1)^j j!·r_k`, the general
derivative residue. -/
theorem gamma_factor_near_pole (k : ℕ) :
    (fun s : ℂ => Complex.Gamma s) =ᶠ[𝓝[≠] (-(k : ℂ))]
      fun s => (Complex.Gamma (s + ((k + 1 : ℕ) : ℂ)) / ∏ j ∈ Finset.range k, (s + (j : ℂ)))
        * (s + (k : ℂ))⁻¹ := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (Metric.ball_mem_nhds (-(k : ℂ)) (show (0 : ℝ) < 1 / 2 by norm_num)), self_mem_nhdsWithin]
    with s hsb hsne
  have hne := ball_avoids hsb hsne
  have hpole : ∀ j : ℕ, j ≤ k → s + (j : ℂ) ≠ 0 := fun j _ h => hne j (by linear_combination h)
  have hprod := gamma_prod k s hpole
  rw [Finset.prod_range_succ] at hprod
  have hk0 : s + (k : ℂ) ≠ 0 := hpole k le_rfl
  have hpk : (∏ j ∈ Finset.range k, (s + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => hpole j (by rw [Finset.mem_range] at hj; omega))
  field_simp
  linear_combination hprod

/-- The analytic extension of the pole of Γ at `−k`: `G̃(s) = Γ(s+k+1)/∏_{j<k}(s+j)`, which agrees with
`(s+k)·Γ(s)` off the pole and extends it analytically across `−k`. -/
noncomputable def gammaExtension (k : ℕ) : ℂ → ℂ :=
  fun s => Complex.Gamma (s + ((k + 1 : ℕ) : ℂ)) / ∏ j ∈ Finset.range k, (s + (j : ℂ))

/-- **The analytic extension evaluates to the residue.**  `G̃(−k) = (−1)^k/k! = r_k`: the value of the
analytic extension of `(s+k)·Γ(s)` at the pole is exactly the residue of Γ there.  Proved from
`gamma_residue` (the residue as a limit), `gamma_factor_near_pole` (the factorization), and continuity
of `G̃` (`contDiffAt_gammaExtension`). -/
theorem gammaExtension_apply_neg (k : ℕ) :
    gammaExtension k (-(k : ℂ)) = (-1) ^ k / (k.factorial : ℂ) := by
  have hcont : ContinuousAt (gammaExtension k) (-(k : ℂ)) :=
    (contDiffAt_gammaExtension k 0).continuousAt
  have h1 : Tendsto (gammaExtension k) (𝓝[≠] (-(k : ℂ))) (𝓝 (gammaExtension k (-(k : ℂ)))) :=
    hcont.continuousWithinAt
  have h2 : Tendsto (gammaExtension k) (𝓝[≠] (-(k : ℂ))) (𝓝 ((-1) ^ k / (k.factorial : ℂ))) := by
    refine (gamma_residue k).congr' ?_
    filter_upwards [gamma_factor_near_pole k, self_mem_nhdsWithin] with s hs hsne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
    have hk0 : s + (k : ℂ) ≠ 0 := fun h => hsne (by linear_combination h)
    simp only [gammaExtension]
    rw [hs]; field_simp
  rw [← tendsto_nhds_unique h1 h2]

/-- **The general derivative residue of Γ.**  `(s+k)^{j+1}·Γ⁽ʲ⁾(s) → (−1)^j·j!·((−1)^k/k!)` as
`s → −k`, for every order `j` and pole `−k`.  This is the full Laurent leading datum of every
derivative of Γ at its poles — the input the `(k!)`-domination step of Hölder consumes.  Proved by the
analytic factorization `Γ = G̃·(s+k)⁻¹` (`gamma_factor_near_pole`), Leibniz (`iteratedDeriv_mul`)
against the simple-pole derivatives (`iteratedDeriv_inv_add_const`), and taking `s → −k` where only the
zeroth Leibniz term (value `G̃(−k) = r_k`, `gammaExtension_apply_neg`) survives. -/
theorem gamma_iteratedDeriv_residue (j k : ℕ) :
    Tendsto (fun s : ℂ => (s + (k:ℂ))^(j+1) * iteratedDeriv j Complex.Gamma s) (𝓝[≠] (-(k:ℂ)))
      (𝓝 ((-1)^j * (j.factorial:ℂ) * ((-1)^k / (k.factorial:ℂ)))) := by
  set G := gammaExtension k with hGdef
  set U := {s : ℂ | ∀ m : ℕ, m ≤ k → s + (m:ℂ) ≠ 0} with hU
  have hfac : ∀ s ∈ U, Complex.Gamma =ᶠ[𝓝 s] G * fun t : ℂ => (t + (k:ℂ))⁻¹ := by
    intro s hs
    have hUopen : IsOpen U := by
      have hEq : U = ⋂ m ∈ Finset.range (k+1), {s : ℂ | s + (m:ℂ) ≠ 0} := by
        ext s; simp only [hU, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
      rw [hEq]; exact isOpen_biInter_finset (fun m _ => isOpen_ne_fun (by fun_prop) continuous_const)
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hs) (fun t ht => ?_)
    have hprod := gamma_prod k t ht
    rw [Finset.prod_range_succ] at hprod
    have hk0 : t + (k:ℂ) ≠ 0 := ht k le_rfl
    have hpk : (∏ m ∈ range k, (t + (m:ℂ))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun m hm => ht m (by rw [mem_range] at hm; omega))
    show Complex.Gamma t = G t * (t + (k:ℂ))⁻¹
    simp only [hGdef, gammaExtension]; field_simp; linear_combination hprod
  -- eventual leibniz identity
  have hev : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)),
      (s + (k:ℂ))^(j+1) * iteratedDeriv j Complex.Gamma s
        = ∑ i ∈ range (j+1),
          (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
            * (s + (k:ℂ))^i := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
      with s hsb hsne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
    have hne := ball_avoids hsb hsne
    have hsU : s ∈ U := fun m _ h => hne m (by linear_combination h)
    have hk0 : s + (k:ℂ) ≠ 0 := fun h => hsne (by linear_combination h)
    have hs1 : ∀ m : ℕ, s + ((k+1:ℕ):ℂ) ≠ -(m:ℂ) :=
      fun m h => hne (m + k + 1) (by push_cast; push_cast at h; linear_combination h)
    have hcdG : ContDiffAt ℂ j G s := by
      rw [hGdef]
      show ContDiffAt ℂ j (fun t : ℂ => Complex.Gamma (t + ((k+1:ℕ):ℂ)) / ∏ m ∈ range k, (t + (m:ℂ))) s
      have hnum : ContDiffAt ℂ j (fun t : ℂ => Complex.Gamma (t + ((k+1:ℕ):ℂ))) s :=
        (contDiffAt_Gamma _ hs1 j).comp s (by fun_prop)
      have hden : ContDiffAt ℂ j (fun t : ℂ => ∏ m ∈ range k, (t + (m:ℂ))) s := by fun_prop
      have hdne : (∏ m ∈ range k, (s + (m:ℂ))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun m hm => hsU m (by rw [mem_range] at hm; omega))
      exact hnum.div hden hdne
    have hcdInv : ContDiffAt ℂ j (fun t => (t + (k:ℂ))⁻¹) s :=
      (by fun_prop : ContDiffAt ℂ j (fun t : ℂ => t + (k:ℂ)) s).inv hk0
    rw [(hfac s hsU).iteratedDeriv_eq, iteratedDeriv_mul (𝕜 := ℂ) hcdG hcdInv, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mem_range, Nat.lt_succ_iff] at hi
    rw [iteratedDeriv_inv_add_const k (j-i) s hk0]
    have hpow : (s + (k:ℂ))^(j+1) * ((s + (k:ℂ))^((j-i)+1))⁻¹ = (s + (k:ℂ))^i := by
      rw [← pow_sub₀ _ hk0 (by omega : (j-i)+1 ≤ j+1)]; congr 1; omega
    linear_combination ((j.choose i : ℂ) * iteratedDeriv i G s * (-1)^(j-i)
      * ((j-i).factorial : ℂ)) * hpow
  -- sum limit
  have hlim : Tendsto (fun s : ℂ => ∑ i ∈ range (j+1),
      (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
        * (s + (k:ℂ))^i) (𝓝[≠] (-(k:ℂ)))
      (𝓝 ((-1)^j * (j.factorial:ℂ) * ((-1)^k / (k.factorial:ℂ)))) := by
    have hterms : Tendsto (fun s : ℂ => ∑ i ∈ range (j+1),
        (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
          * (s + (k:ℂ))^i) (𝓝[≠] (-(k:ℂ)))
        (𝓝 (∑ i ∈ range (j+1),
          (j.choose i : ℂ) * (iteratedDeriv i G (-(k:ℂ)) * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
            * ((-(k:ℂ)) + (k:ℂ))^i)) := by
      apply tendsto_finsetSum
      intro i _
      have hci : ContinuousAt (iteratedDeriv i G) (-(k:ℂ)) :=
        continuousAt_iteratedDeriv_of_contDiffAt (by rw [hGdef]; exact contDiffAt_gammaExtension k i)
      have hpi : Tendsto (fun s : ℂ => (s + (k:ℂ))^i) (𝓝[≠] (-(k:ℂ))) (𝓝 (((-(k:ℂ)) + (k:ℂ))^i)) :=
        ((continuous_id.add continuous_const).pow i).continuousAt.continuousWithinAt
      exact (((tendsto_const_nhds).mul (hci.continuousWithinAt.mul tendsto_const_nhds)).mul hpi)
    have hval : (∑ i ∈ range (j+1),
        (j.choose i : ℂ) * (iteratedDeriv i G (-(k:ℂ)) * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
          * ((-(k:ℂ)) + (k:ℂ))^i)
        = (-1)^j * (j.factorial:ℂ) * ((-1)^k / (k.factorial:ℂ)) := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, mul_one, iteratedDeriv_zero, Nat.choose_zero_right, Nat.cast_one,
          one_mul, Nat.sub_zero]
        rw [hGdef, gammaExtension_apply_neg]; ring
      · intro i _ hi0; rw [neg_add_cancel, zero_pow hi0, mul_zero]
      · intro h; simp at h
    rw [hval] at hterms
    exact hterms
  exact hlim.congr' (hev.mono (fun _ h => h.symm))

/-- **The residue of a differential monomial.**  For a finite set of orders `S` with exponents `e`,
`∏_{j∈S} ((s+k)^{j+1}·Γ⁽ʲ⁾(s))^{e_j} → ∏_{j∈S} ((−1)^j·j!·r_k)^{e_j}` as `s → −k` — the Laurent leading
datum of a differential monomial, a product of powers of `gamma_iteratedDeriv_residue`.  Summing these
over the top-weighted-degree monomials of a differential polynomial `P` gives the leading Laurent
coefficient of `P(s,Γ,…,Γ⁽ⁿ⁾)` at `−k`; the `(k!)`-domination then finishes Hölder. -/
theorem gamma_diffMonomial_residue (k : ℕ) (S : Finset ℕ) (e : ℕ → ℕ) :
    Tendsto (fun s : ℂ => ∏ j ∈ S, ((s + (k : ℂ)) ^ (j + 1) * iteratedDeriv j Complex.Gamma s) ^ (e j))
      (𝓝[≠] (-(k : ℂ)))
      (𝓝 (∏ j ∈ S, ((-1) ^ j * (j.factorial : ℂ) * ((-1) ^ k / (k.factorial : ℂ))) ^ (e j))) := by
  apply tendsto_finsetProd
  intro j _
  exact (gamma_iteratedDeriv_residue j k).pow (e j)

/-- **Domination finisher.**  A polynomial whose values `p(−k)` tend to `0` as `k → ∞` is the zero
polynomial (a nonzero polynomial has `‖p(−k)‖ → ∞` if nonconstant, or a nonzero constant value).  This
is the arithmetic step that closes the Hölder domination: once the factorial growth forces the top
coefficient `c(−k) → 0`, this lemma concludes `c ≡ 0`, contradicting its being the top coefficient. -/
theorem poly_eval_neg_tendsto_zero_imp_zero (p : Polynomial ℂ)
    (h : Tendsto (fun k : ℕ => p.eval (-(k : ℂ))) atTop (𝓝 0)) : p = 0 := by
  by_contra hp
  rcases eq_or_ne p.natDegree 0 with hd | hd
  · obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hd
    simp only [Polynomial.eval_C] at h
    have hc0 : (0 : ℂ) = c := tendsto_nhds_unique h tendsto_const_nhds
    exact hp (by rw [← hc0, map_zero])
  · have hpos : 0 < p.natDegree := Nat.pos_of_ne_zero hd
    have hz : Tendsto (fun k : ℕ => ‖-(k : ℂ)‖) atTop atTop := by
      simp only [norm_neg, Complex.norm_natCast]; exact tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun k : ℕ => ‖p.eval (-(k : ℂ))‖) atTop atTop :=
      p.tendsto_norm_atTop (Polynomial.natDegree_pos_iff_degree_pos.mp hpos) hz
    have h2 : Tendsto (fun k : ℕ => ‖p.eval (-(k : ℂ))‖) atTop (𝓝 0) := by
      have hfun :
          (fun k : ℕ => ‖p.eval (-(k : ℂ))‖) =
            (fun a : ℂ => ‖a‖) ∘ fun k : ℕ => p.eval (-(k : ℂ)) := by
        funext k
        rfl
      rw [hfun]
      simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).comp h
    exact not_tendsto_nhds_of_tendsto_atTop h1 0 h2

/-- **Γ is not D-finite of order 1 (first-order linear Hölder).**  Γ satisfies no linear differential
relation `c₀(s)·Γ(s) + c₁(s)·Γ′(s) = 0` with polynomial coefficients `c₀, c₁` not both zero —
equivalently, `Γ′/Γ = digamma` is not a rational function.  Proved directly from the residue calculus:
multiplying by `(s+k)²`, the `Γ` term vanishes (`(s+k)²·Γ → 0`) while the `Γ′` term survives
(`gamma_deriv_residue`: `(s+k)²·Γ′ → −r_k`), forcing `c₁(−k) = 0` at every pole, hence `c₁ ≡ 0`; then
`c₀·Γ = 0` with `Γ ≠ 0` forces `c₀ ≡ 0`.  The linear case of Hölder's theorem, with no combinatorial
weighted-degree machinery. -/
theorem gamma_no_linear_relation (c0 c1 : Polynomial ℂ) (hc : c0 ≠ 0 ∨ c1 ≠ 0) :
    ∃ s : ℂ, c0.eval s * Complex.Gamma s + c1.eval s * deriv Complex.Gamma s ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  -- c1 vanishes at every pole -k
  have hck : ∀ k : ℕ, c1.eval (-(k:ℂ)) = 0 := by
    intro k
    have rk : ℂ := (-1)^k / (k.factorial : ℂ)
    have hrk : ((-1)^k / (k.factorial : ℂ)) ≠ 0 := by
      apply div_ne_zero
      · exact pow_ne_zero k (by norm_num)
      · exact_mod_cast Nat.factorial_ne_zero k
    -- the whole thing ·(s+k)² ≡ 0
    have h0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(2 : ℕ)
        * (c0.eval s * Complex.Gamma s + c1.eval s * deriv Complex.Gamma s))
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards with s; rw [hcon s]; ring
    -- (s+k)²·Γ → 0
    have hg2 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(2 : ℕ) * Complex.Gamma s) (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hz : Tendsto (fun s : ℂ => s + (k:ℂ)) (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
        have : Tendsto (fun s : ℂ => s + (k:ℂ)) (𝓝 (-(k:ℂ))) (𝓝 ((-(k:ℂ)) + (k:ℂ))) :=
          (continuous_id.add continuous_const).continuousAt
        rw [neg_add_cancel] at this; exact this.mono_left nhdsWithin_le_nhds
      have := hz.mul (gamma_residue k)
      simp only [zero_mul] at this
      refine this.congr' ?_; filter_upwards with s; ring
    -- assemble the other limit
    have hA : Tendsto (fun s : ℂ => c0.eval s * ((s + (k:ℂ))^(2 : ℕ) * Complex.Gamma s))
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hc0 : Tendsto (fun s : ℂ => c0.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c0.eval (-(k:ℂ)))) :=
        (c0.continuous.continuousAt).continuousWithinAt
      have := hc0.mul hg2; simpa using this
    have hB : Tendsto (fun s : ℂ => c1.eval s * ((s + (k:ℂ))^(2 : ℕ) * deriv Complex.Gamma s))
        (𝓝[≠] (-(k:ℂ))) (𝓝 (c1.eval (-(k:ℂ)) * (-((-1)^k / (k.factorial : ℂ))))) := by
      have hc1 : Tendsto (fun s : ℂ => c1.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c1.eval (-(k:ℂ)))) :=
        (c1.continuous.continuousAt).continuousWithinAt
      have hd := gamma_deriv_residue k
      exact hc1.mul hd
    have hsum := hA.add hB
    rw [zero_add] at hsum
    have heq : Tendsto (fun s : ℂ => (s + (k:ℂ))^(2 : ℕ)
        * (c0.eval s * Complex.Gamma s + c1.eval s * deriv Complex.Gamma s))
        (𝓝[≠] (-(k:ℂ))) (𝓝 (c1.eval (-(k:ℂ)) * (-((-1)^k / (k.factorial : ℂ))))) := by
      refine hsum.congr' ?_; filter_upwards with s; ring
    have := tendsto_nhds_unique h0 heq
    have hz2 : c1.eval (-(k:ℂ)) * (-((-1)^k / (k.factorial : ℂ))) = 0 := this.symm
    rcases mul_eq_zero.mp hz2 with h | h
    · exact h
    · exact absurd (neg_eq_zero.mp h) hrk
  -- c1 = 0 (infinite roots)
  have hc1z : c1 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => -(k:ℂ))
      (fun a b hab => by simpa using hab)
    intro k; exact hck k
  -- then c0 Γ = 0, Γ ≠ 0, so c0 = 0
  have hc0z : c0 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k:ℂ) + 1)
      (fun a b hab => by simpa using hab)
    intro k
    have hΓne : Complex.Gamma ((k:ℂ) + 1) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.neg_re] at hr
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      linarith
    have hrel := hcon ((k:ℂ) + 1)
    rw [hc1z] at hrel; simp only [Polynomial.eval_zero, zero_mul, add_zero] at hrel
    exact (mul_eq_zero.mp hrel).resolve_right hΓne
  rcases hc with h | h
  · exact h hc0z
  · exact h hc1z

/-- **Not-holonomic engine, top step.**  Let `f` have, at each pole `−k`, iterated-derivative residues
`(s+k)^{i+1}·f⁽ⁱ⁾(s) → L(i,k)` with every `L(i,k) ≠ 0`.  Then any linear relation `∑_{j≤n} c_j·f⁽ʲ⁾ ≡ 0`
forces the top coefficient `c_n ≡ 0`: multiplying by `(s+k)^{n+1}` writes each term as
`c_j(s)·(s+k)^{n−j}·((s+k)^{j+1}·f⁽ʲ⁾(s))`, and `(s+k)^{n−j} → 0` for `j < n`, so only `j = n` survives,
giving `c_n(−k)·L(n,k) = 0`, hence `c_n(−k) = 0` at every pole and `c_n ≡ 0`. -/
theorem linear_top_zero_of_residues (f : ℂ → ℂ) (L : ℕ → ℕ → ℂ) (hL : ∀ i k, L i k ≠ 0)
    (hres : ∀ i k : ℕ, Tendsto (fun s : ℂ => (s + (k:ℂ))^(i+1) * iteratedDeriv i f s)
      (𝓝[≠] (-(k:ℂ))) (𝓝 (L i k)))
    (n : ℕ) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s = 0) :
    c n = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => -(k:ℂ))
    (fun a b hab => by simpa using hab)
  intro k
  have h0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(n+1)
      * ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s)
      (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with s; rw [hrel s]; ring
  have hfun : (fun s : ℂ => (s + (k:ℂ))^(n+1)
      * ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s)
      = fun s : ℂ => ∑ j ∈ range (n+1),
          (c j).eval s * ((s + (k:ℂ))^(n-j) * ((s + (k:ℂ))^(j+1) * iteratedDeriv j f s)) := by
    funext s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [mem_range, Nat.lt_succ_iff] at hj
    rw [← mul_assoc ((s + (k:ℂ))^(n-j)), ← pow_add, show (n-j)+(j+1) = n+1 by omega]
    ring
  have hterms : Tendsto (fun s : ℂ => ∑ j ∈ range (n+1),
      (c j).eval s * ((s + (k:ℂ))^(n-j) * ((s + (k:ℂ))^(j+1) * iteratedDeriv j f s)))
      (𝓝[≠] (-(k:ℂ)))
      (𝓝 (∑ j ∈ range (n+1), (c j).eval (-(k:ℂ)) * (((-(k:ℂ)) + (k:ℂ))^(n-j) * L j k))) := by
    apply tendsto_finsetSum
    intro j _
    have hcj : Tendsto (fun s : ℂ => (c j).eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 ((c j).eval (-(k:ℂ)))) :=
      (c j).continuous.continuousAt.continuousWithinAt
    have hpow : Tendsto (fun s : ℂ => (s + (k:ℂ))^(n-j)) (𝓝[≠] (-(k:ℂ)))
        (𝓝 (((-(k:ℂ)) + (k:ℂ))^(n-j))) :=
      ((continuous_id.add continuous_const).pow (n-j)).continuousAt.continuousWithinAt
    exact hcj.mul (hpow.mul (hres j k))
  rw [hfun] at h0
  have hval : (∑ j ∈ range (n+1), (c j).eval (-(k:ℂ)) * (((-(k:ℂ)) + (k:ℂ))^(n-j) * L j k))
      = (c n).eval (-(k:ℂ)) * L n k := by
    rw [Finset.sum_eq_single n]
    · rw [neg_add_cancel, Nat.sub_self, pow_zero, one_mul]
    · intro j hjmem hjn
      rw [mem_range, Nat.lt_succ_iff] at hjmem
      have hnj : n - j ≠ 0 := by omega
      rw [neg_add_cancel, zero_pow hnj, zero_mul, mul_zero]
    · intro h; simp at h
  rw [hval] at hterms
  have := tendsto_nhds_unique h0 hterms
  rcases mul_eq_zero.mp this.symm with h | h
  · exact h
  · exact absurd h (hL n k)

/-- **Not-holonomic from nonvanishing derivative residues.**  If `f`'s iterated derivatives have, at
each pole `−k`, residues `(s+k)^{i+1}·f⁽ⁱ⁾(s) → L(i,k)` with every `L(i,k) ≠ 0`, then `f` satisfies no
linear differential equation with polynomial coefficients: `∑_{j≤n} c_j·f⁽ʲ⁾ ≡ 0` forces every `c_j ≡ 0`.
Induction on the order via `linear_top_zero_of_residues`.  This is the abstract pole-domination engine
behind "not holonomic": it needs only that each derivative has a genuine pole of the expected order at a
sequence of points. -/
theorem not_holonomic_of_residues (f : ℂ → ℂ) (L : ℕ → ℕ → ℂ) (hL : ∀ i k, L i k ≠ 0)
    (hres : ∀ i k : ℕ, Tendsto (fun s : ℂ => (s + (k:ℂ))^(i+1) * iteratedDeriv i f s)
      (𝓝[≠] (-(k:ℂ))) (𝓝 (L i k))) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  intro n
  induction n with
  | zero =>
    intro c hrel j hj
    rw [mem_range, Nat.lt_one_iff] at hj; subst hj
    exact linear_top_zero_of_residues f L hL hres 0 c hrel
  | succ m ih =>
    intro c hrel
    have htop : c (m+1) = 0 := linear_top_zero_of_residues f L hL hres (m+1) c hrel
    have hrel' : ∀ s, ∑ j ∈ range (m+1), (c j).eval s * iteratedDeriv j f s = 0 := by
      intro s; have h := hrel s; rw [Finset.sum_range_succ, htop] at h
      simp only [Polynomial.eval_zero, zero_mul, add_zero] at h; exact h
    intro j hj; rw [mem_range, Nat.lt_succ_iff] at hj
    rcases eq_or_lt_of_le hj with hjm | hjm
    · rw [hjm]; exact htop
    · exact ih c hrel' j (mem_range.mpr (by omega))

/-- **Γ is not holonomic (the full linear Hölder theorem).**  Γ satisfies no linear differential
equation with polynomial coefficients of any order: if `∑_{j≤n} c_j(s)·Γ⁽ʲ⁾(s) ≡ 0` then every `c_j ≡ 0`.
The instance of `not_holonomic_of_residues` for Γ, whose derivative residues `(−1)^j·j!·((−1)^k/k!)`
(`gamma_iteratedDeriv_residue`) are all nonzero.  The entire *linear* case of Hölder's hypertranscendence
theorem, from the residue calculus with no combinatorial weighted-degree machinery. -/
theorem gamma_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j Complex.Gamma s = 0) →
    ∀ j ∈ range (n+1), c j = 0 :=
  not_holonomic_of_residues Complex.Gamma
    (fun i k => (-1)^i * (i.factorial:ℂ) * ((-1)^k / (k.factorial:ℂ)))
    (fun i k => mul_ne_zero (mul_ne_zero (pow_ne_zero i (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero i))
      (div_ne_zero (pow_ne_zero k (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)))
    gamma_iteratedDeriv_residue

/-- **Unwinding the digamma functional equation.**  Iterating `ψ(s+1) = ψ(s) + 1/s`
(`digamma_apply_add_one`) gives `ψ(s+k+1) = ψ(s) + ∑_{j=0}^{k} 1/(s+j)` for `s` off the poles `−ℕ`.
Equivalently `ψ(s) = ψ(s+k+1) − ∑_{j≤k} 1/(s+j)`: this exhibits the simple pole of `ψ` at `−k` as the
`−1/(s+k)` term, the digamma analogue of `gamma_prod`, and the starting point for the residues of the
polygamma functions `ψ⁽ⁱ⁾` at `−k`. -/
theorem digamma_unwind (k : ℕ) (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m:ℂ)) :
    Complex.digamma (s + ((k+1:ℕ):ℂ)) = Complex.digamma s + ∑ j ∈ range (k+1), (s + (j:ℂ))⁻¹ := by
  induction k with
  | zero =>
    rw [show s + ((0+1:ℕ):ℂ) = s + 1 by push_cast; ring, Complex.digamma_apply_add_one s hs,
        Finset.sum_range_one, Nat.cast_zero, add_zero]
  | succ n ih =>
    have hne' : ∀ m : ℕ, s + ((n+1:ℕ):ℂ) ≠ -(m:ℂ) :=
      fun m h => hs (m+n+1) (by push_cast; push_cast at h; linear_combination h)
    rw [show s + ((n+1+1:ℕ):ℂ) = (s + ((n+1:ℕ):ℂ)) + 1 by push_cast; ring,
        Complex.digamma_apply_add_one _ hne', ih,
        Finset.sum_range_succ (fun j => (s + (j:ℂ))⁻¹) (n+1)]
    push_cast; ring

/-- **Derivative residues from a simple-pole factorization.**  If `f = G·(s+k)⁻¹` on an open set `U`
approaching the pole `−k` (`hfac`, `hUnhds`), with `G` smooth on `U` and at `−k` (`hGU`, `hGk`) and
`s+k ≠ 0` on `U` (`hkne`), then `(s+k)^{j+1}·f⁽ʲ⁾(s) → G(−k)·(−1)^j·j!` as `s → −k`, for every order `j`.
The Laurent leading datum of every derivative of a simple pole: Leibniz against the derivatives of
`(s+k)⁻¹`, and only the zeroth term (value `G(−k)`) survives the limit.  The analytic engine behind the
derivative residues of `Γ`, `digamma`, and any meromorphic function with a simple pole. -/
theorem iteratedDeriv_residue_of_factor (f G : ℂ → ℂ) (k : ℕ) (U : Set ℂ)
    (hkne : ∀ s ∈ U, s + (k:ℂ) ≠ 0)
    (hUnhds : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), s ∈ U)
    (hGU : ∀ s ∈ U, ∀ n : ℕ, ContDiffAt ℂ n G s)
    (hGk : ∀ n : ℕ, ContDiffAt ℂ n G (-(k:ℂ)))
    (hfac : ∀ s ∈ U, f =ᶠ[𝓝 s] G * fun t : ℂ => (t + (k:ℂ))⁻¹)
    (j : ℕ) :
    Tendsto (fun s : ℂ => (s + (k:ℂ))^(j+1) * iteratedDeriv j f s) (𝓝[≠] (-(k:ℂ)))
      (𝓝 (G (-(k:ℂ)) * ((-1)^j * (j.factorial:ℂ)))) := by
  have hev : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)),
      (s + (k:ℂ))^(j+1) * iteratedDeriv j f s
        = ∑ i ∈ range (j+1),
          (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
            * (s + (k:ℂ))^i := by
    filter_upwards [hUnhds] with s hsU
    have hk0 : s + (k:ℂ) ≠ 0 := hkne s hsU
    have hcdG : ContDiffAt ℂ j G s := hGU s hsU j
    have hcdInv : ContDiffAt ℂ j (fun t => (t + (k:ℂ))⁻¹) s :=
      (by fun_prop : ContDiffAt ℂ j (fun t : ℂ => t + (k:ℂ)) s).inv hk0
    rw [(hfac s hsU).iteratedDeriv_eq, iteratedDeriv_mul (𝕜 := ℂ) hcdG hcdInv, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mem_range, Nat.lt_succ_iff] at hi
    rw [iteratedDeriv_inv_add_const k (j-i) s hk0]
    have hpow : (s + (k:ℂ))^(j+1) * ((s + (k:ℂ))^((j-i)+1))⁻¹ = (s + (k:ℂ))^i := by
      rw [← pow_sub₀ _ hk0 (by omega : (j-i)+1 ≤ j+1)]; congr 1; omega
    linear_combination ((j.choose i : ℂ) * iteratedDeriv i G s * (-1)^(j-i)
      * ((j-i).factorial : ℂ)) * hpow
  have hlim : Tendsto (fun s : ℂ => ∑ i ∈ range (j+1),
      (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
        * (s + (k:ℂ))^i) (𝓝[≠] (-(k:ℂ)))
      (𝓝 (G (-(k:ℂ)) * ((-1)^j * (j.factorial:ℂ)))) := by
    have hterms : Tendsto (fun s : ℂ => ∑ i ∈ range (j+1),
        (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
          * (s + (k:ℂ))^i) (𝓝[≠] (-(k:ℂ)))
        (𝓝 (∑ i ∈ range (j+1),
          (j.choose i : ℂ) * (iteratedDeriv i G (-(k:ℂ)) * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
            * ((-(k:ℂ)) + (k:ℂ))^i)) := by
      apply tendsto_finsetSum
      intro i _
      have hci : ContinuousAt (iteratedDeriv i G) (-(k:ℂ)) :=
        continuousAt_iteratedDeriv_of_contDiffAt (hGk i)
      have hpi : Tendsto (fun s : ℂ => (s + (k:ℂ))^i) (𝓝[≠] (-(k:ℂ))) (𝓝 (((-(k:ℂ)) + (k:ℂ))^i)) :=
        ((continuous_id.add continuous_const).pow i).continuousAt.continuousWithinAt
      exact (((tendsto_const_nhds).mul (hci.continuousWithinAt.mul tendsto_const_nhds)).mul hpi)
    have hval : (∑ i ∈ range (j+1),
        (j.choose i : ℂ) * (iteratedDeriv i G (-(k:ℂ)) * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
          * ((-(k:ℂ)) + (k:ℂ))^i)
        = G (-(k:ℂ)) * ((-1)^j * (j.factorial:ℂ)) := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, mul_one, iteratedDeriv_zero, Nat.choose_zero_right, Nat.cast_one,
          one_mul, Nat.sub_zero]
      · intro i _ hi0; rw [neg_add_cancel, zero_pow hi0, mul_zero]
      · intro h; simp at h
    rw [hval] at hterms
    exact hterms
  exact hlim.congr' (hev.mono (fun _ h => h.symm))

/-- The analytic extension of the pole of `digamma` at `−k`: `G_ψ(s) = (s+k)·(ψ(s+k+1) − ∑_{j<k}1/(s+j)) − 1`,
which agrees with `(s+k)·ψ(s)` off the pole (`digamma_factor`) and extends it across `−k` with value `−1`. -/
noncomputable def digammaExtension (k : ℕ) : ℂ → ℂ :=
  fun s => (s + (k:ℂ)) * (Complex.digamma (s + ((k+1:ℕ):ℂ)) - ∑ j ∈ range k, (s + (j:ℂ))⁻¹) - 1

/-- The digamma analytic extension evaluates to the residue: `G_ψ(−k) = −1` (the `(s+k)` prefactor
kills the finite bracket). -/
theorem digammaExtension_apply_neg (k : ℕ) : digammaExtension k (-(k:ℂ)) = -1 := by
  simp only [digammaExtension, neg_add_cancel, zero_mul, zero_sub]

-- facts on the ball
/-- The digamma analytic extension `G_ψ` is `C^n` wherever `ψ(·+k+1)` is regular (`hdig`) and the poles
`−0,…,−(k−1)` are avoided (`hj`) — in particular on a punctured ball about `−k` and at `−k` itself. -/
theorem digamma_extension_smooth {k : ℕ} {s : ℂ}
    (hdig : ∀ m : ℕ, s + ((k+1:ℕ):ℂ) ≠ -(m:ℂ)) (hj : ∀ j ∈ range k, s + (j:ℂ) ≠ 0) (n : ℕ) :
    ContDiffAt ℂ n (digammaExtension k) s := by
  have hdd : ContDiffAt ℂ n (fun t : ℂ => Complex.digamma (t + ((k+1:ℕ):ℂ))) s :=
    (contDiffAt_digamma_n _ hdig n).comp s (by fun_prop)
  have hsum : ContDiffAt ℂ n (fun t : ℂ => ∑ j ∈ range k, (t + (j:ℂ))⁻¹) s := by
    apply ContDiffAt.sum
    intro j hjm
    exact (by fun_prop : ContDiffAt ℂ n (fun t : ℂ => t + (j:ℂ)) s).inv (hj j hjm)
  exact ((by fun_prop : ContDiffAt ℂ n (fun t : ℂ => t + (k:ℂ)) s).mul (hdd.sub hsum)).sub contDiffAt_const

/-- **The digamma pole factorizes:** `ψ(s) = G_ψ(s)·(s+k)⁻¹` off the poles, from `digamma_unwind`. -/
theorem digamma_factor {k : ℕ} {s : ℂ} (hne : ∀ m : ℕ, s ≠ -(m:ℂ)) :
    Complex.digamma s = digammaExtension k s * (s + (k:ℂ))⁻¹ := by
  have hk0 : s + (k:ℂ) ≠ 0 := fun h => hne k (by linear_combination h)
  have hunw := digamma_unwind k s hne
  have hfe : Complex.digamma s = Complex.digamma (s + ((k+1:ℕ):ℂ)) - ∑ j ∈ range (k+1), (s + (j:ℂ))⁻¹ := by
    rw [hunw]; ring
  rw [digammaExtension, hfe, Finset.sum_range_succ]
  field_simp
  ring

/-- **The general polygamma residue.**  `(s+k)^{i+1}·ψ⁽ⁱ⁾(s) → (−1)^{i+1}·i!` as `s → −k`, for every
order `i` and pole `−k`: the digamma instance of `iteratedDeriv_residue_of_factor` via the analytic
extension `G_ψ` (value `G_ψ(−k) = −1`).  The Laurent leading datum of every derivative of digamma. -/
theorem digamma_iteratedDeriv_residue (j k : ℕ) :
    Tendsto (fun s : ℂ => (s + (k:ℂ))^(j+1) * iteratedDeriv j Complex.digamma s) (𝓝[≠] (-(k:ℂ)))
      (𝓝 ((-1)^(j+1) * (j.factorial:ℂ))) := by
  have hval : digammaExtension k (-(k:ℂ)) * ((-1)^j * (j.factorial:ℂ)) = (-1)^(j+1) * (j.factorial:ℂ) := by
    rw [digammaExtension_apply_neg]; ring
  rw [← hval]
  refine iteratedDeriv_residue_of_factor Complex.digamma (digammaExtension k) k
    (Metric.ball (-(k:ℂ)) (1/2) \ {-(k:ℂ)}) ?_ ?_ ?_ ?_ ?_ j
  · exact fun s hs h => hs.2 (by rw [Set.mem_singleton_iff]; linear_combination h)
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
      with s hsb hsne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
    exact ⟨hsb, hsne⟩
  · intro s hs n
    have hav := ball_avoids hs.1 (by simpa using hs.2)
    exact digamma_extension_smooth
      (fun m h => hav (m+k+1) (by push_cast; push_cast at h; linear_combination h))
      (fun j hjm => fun h => hav j (by rw [mem_range] at hjm; linear_combination h)) n
  · intro n
    refine digamma_extension_smooth (fun m h => ?_) (fun j hjm h => ?_) n
    · have hr := congrArg Complex.re h
      simp only [Complex.add_re, Complex.neg_re, Complex.natCast_re] at hr
      have : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      push_cast at hr; linarith
    · rw [mem_range] at hjm
      have : (k:ℂ) = (j:ℂ) := by linear_combination -h
      exact absurd (by exact_mod_cast this : k = j) (by omega)
  · intro s hs
    have hU : IsOpen (Metric.ball (-(k:ℂ)) (1/2) \ {-(k:ℂ)}) :=
      Metric.isOpen_ball.sdiff isClosed_singleton
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds hs) (fun t ht => ?_)
    show Complex.digamma t = digammaExtension k t * (t + (k:ℂ))⁻¹
    exact digamma_factor (ball_avoids ht.1 (by simpa using ht.2))

/-- **Digamma is not holonomic.**  `ψ = Γ′/Γ` satisfies no linear differential equation with polynomial
coefficients of any order.  The second instance of `not_holonomic_of_residues` (after Γ), with the
nonvanishing polygamma residues `(−1)^{i+1}·i!`.  A second fundamental function proven not D-finite by
the same pole-domination engine. -/
theorem digamma_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j Complex.digamma s = 0) →
    ∀ j ∈ range (n+1), c j = 0 :=
  not_holonomic_of_residues Complex.digamma (fun i _ => (-1)^(i+1) * (i.factorial:ℂ))
    (fun i _ => mul_ne_zero (pow_ne_zero (i+1) (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero i))
    digamma_iteratedDeriv_residue

/-- `iteratedDeriv i (iteratedDeriv m f) = iteratedDeriv (i+m) f`: iterated derivatives compose additively. -/
theorem iteratedDeriv_comp_iterate (f : ℂ → ℂ) (i m : ℕ) :
    iteratedDeriv i (iteratedDeriv m f) = iteratedDeriv (i + m) f := by
  induction i with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, ← iteratedDeriv_succ]; congr 1; omega

/-- **Higher-order-pole not-holonomic engine, top step.**  The order-`P` generalization of
`linear_top_zero_of_residues`: if each `f⁽ⁱ⁾` has a pole of order `i+P` at every `−k` with nonvanishing
leading coefficient `L(i,k)` (`(s+k)^{i+P}·f⁽ⁱ⁾ → L(i,k) ≠ 0`), then any linear relation
`∑_{j≤n} c_j·f⁽ʲ⁾ ≡ 0` forces the top coefficient `c_n ≡ 0` (`×(s+k)^{n+P}`, only `j=n` survives). -/
theorem linear_top_zero_of_residues_order (f : ℂ → ℂ) (P : ℕ) (L : ℕ → ℕ → ℂ)
    (hL : ∀ i k, L i k ≠ 0)
    (hres : ∀ i k : ℕ, Tendsto (fun s : ℂ => (s + (k:ℂ))^(i+P) * iteratedDeriv i f s)
      (𝓝[≠] (-(k:ℂ))) (𝓝 (L i k)))
    (n : ℕ) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s = 0) :
    c n = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => -(k:ℂ))
    (fun a b hab => by simpa using hab)
  intro k
  have h0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(n+P)
      * ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s)
      (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with s; rw [hrel s]; ring
  have hfun : (fun s : ℂ => (s + (k:ℂ))^(n+P)
      * ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s)
      = fun s : ℂ => ∑ j ∈ range (n+1),
          (c j).eval s * ((s + (k:ℂ))^(n-j) * ((s + (k:ℂ))^(j+P) * iteratedDeriv j f s)) := by
    funext s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [mem_range, Nat.lt_succ_iff] at hj
    rw [← mul_assoc ((s + (k:ℂ))^(n-j)), ← pow_add, show (n-j)+(j+P) = n+P by omega]
    ring
  have hterms : Tendsto (fun s : ℂ => ∑ j ∈ range (n+1),
      (c j).eval s * ((s + (k:ℂ))^(n-j) * ((s + (k:ℂ))^(j+P) * iteratedDeriv j f s)))
      (𝓝[≠] (-(k:ℂ)))
      (𝓝 (∑ j ∈ range (n+1), (c j).eval (-(k:ℂ)) * (((-(k:ℂ)) + (k:ℂ))^(n-j) * L j k))) := by
    apply tendsto_finsetSum
    intro j _
    have hcj : Tendsto (fun s : ℂ => (c j).eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 ((c j).eval (-(k:ℂ)))) :=
      (c j).continuous.continuousAt.continuousWithinAt
    have hpow : Tendsto (fun s : ℂ => (s + (k:ℂ))^(n-j)) (𝓝[≠] (-(k:ℂ)))
        (𝓝 (((-(k:ℂ)) + (k:ℂ))^(n-j))) :=
      ((continuous_id.add continuous_const).pow (n-j)).continuousAt.continuousWithinAt
    exact hcj.mul (hpow.mul (hres j k))
  rw [hfun] at h0
  have hval : (∑ j ∈ range (n+1), (c j).eval (-(k:ℂ)) * (((-(k:ℂ)) + (k:ℂ))^(n-j) * L j k))
      = (c n).eval (-(k:ℂ)) * L n k := by
    rw [Finset.sum_eq_single n]
    · rw [neg_add_cancel, Nat.sub_self, pow_zero, one_mul]
    · intro j hjmem hjn
      rw [mem_range, Nat.lt_succ_iff] at hjmem
      have hnj : n - j ≠ 0 := by omega
      rw [neg_add_cancel, zero_pow hnj, zero_mul, mul_zero]
    · intro h; simp at h
  rw [hval] at hterms
  have := tendsto_nhds_unique h0 hterms
  rcases mul_eq_zero.mp this.symm with h | h
  · exact h
  · exact absurd h (hL n k)

/-- **Not holonomic from order-`P` pole residues.**  A function whose `i`-th derivative has a pole of
order exactly `i+P` at every `−k` with nonvanishing leading coefficient satisfies no linear ODE with
polynomial coefficients.  The order-`P` generalization of `not_holonomic_of_residues` (which is `P=1`),
covering functions with poles of any fixed order — e.g. the polygamma functions. -/
theorem not_holonomic_of_residues_order (f : ℂ → ℂ) (P : ℕ) (L : ℕ → ℕ → ℂ) (hL : ∀ i k, L i k ≠ 0)
    (hres : ∀ i k : ℕ, Tendsto (fun s : ℂ => (s + (k:ℂ))^(i+P) * iteratedDeriv i f s)
      (𝓝[≠] (-(k:ℂ))) (𝓝 (L i k))) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  intro n
  induction n with
  | zero =>
    intro c hrel j hj
    rw [mem_range, Nat.lt_one_iff] at hj; subst hj
    exact linear_top_zero_of_residues_order f P L hL hres 0 c hrel
  | succ m ih =>
    intro c hrel
    have htop : c (m+1) = 0 := linear_top_zero_of_residues_order f P L hL hres (m+1) c hrel
    have hrel' : ∀ s, ∑ j ∈ range (m+1), (c j).eval s * iteratedDeriv j f s = 0 := by
      intro s; have h := hrel s; rw [Finset.sum_range_succ, htop] at h
      simp only [Polynomial.eval_zero, zero_mul, add_zero] at h; exact h
    intro j hj; rw [mem_range, Nat.lt_succ_iff] at hj
    rcases eq_or_lt_of_le hj with hjm | hjm
    · rw [hjm]; exact htop
    · exact ih c hrel' j (mem_range.mpr (by omega))

/-- **Every polygamma function is not holonomic.**  For each `M`, `ψ⁽ᴹ⁾ = digamma⁽ᴹ⁾` satisfies no
linear differential equation with polynomial coefficients: it has a pole of order `M+1` at every `−k`,
so the `M`-th derivative's `i`-th derivative is `ψ⁽ⁱ⁺ᴹ⁾` with residue `(−1)^{i+M+1}·(i+M)! ≠ 0`
(`digamma_iteratedDeriv_residue`), an instance of `not_holonomic_of_residues_order` at pole order `M+1`.
An infinite family of fundamental functions proven not D-finite by the higher-order-pole engine. -/
theorem polygamma_not_holonomic (M : ℕ) : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j (iteratedDeriv M Complex.digamma) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  apply not_holonomic_of_residues_order (iteratedDeriv M Complex.digamma) (M+1)
    (fun i k => (-1)^(i+M+1) * ((i+M).factorial : ℂ))
    (fun i k => mul_ne_zero (pow_ne_zero (i+M+1) (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero (i+M)))
  intro i k
  have hcomp : iteratedDeriv i (iteratedDeriv M Complex.digamma) = iteratedDeriv (i+M) Complex.digamma :=
    iteratedDeriv_comp_iterate Complex.digamma i M
  rw [hcomp]
  have hd := digamma_iteratedDeriv_residue (i+M) k
  have hpe : i + (M + 1) = (i + M) + 1 := by omega
  rw [hpe]
  exact hd

/-- **Master not-holonomic engine, top step.**  Arbitrary pole *locations* `p k` (injective) and pole
*order* `P`: if each `f⁽ⁱ⁾` has a pole of order `i+P` at every `p k` with nonvanishing leading
coefficient (`(s − p k)^{i+P}·f⁽ⁱ⁾ → L(i,k) ≠ 0`), then a relation `∑_{j≤n} c_j·f⁽ʲ⁾ ≡ 0` forces
`c_n ≡ 0`. -/
theorem linear_top_zero_master (f : ℂ → ℂ) (p : ℕ → ℂ) (hp : Function.Injective p) (P : ℕ)
    (L : ℕ → ℕ → ℂ) (hL : ∀ i k, L i k ≠ 0)
    (hres : ∀ i k : ℕ, Tendsto (fun s : ℂ => (s - p k)^(i+P) * iteratedDeriv i f s)
      (𝓝[≠] (p k)) (𝓝 (L i k)))
    (n : ℕ) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s = 0) :
    c n = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := p) hp
  intro k
  have h0 : Tendsto (fun s : ℂ => (s - p k)^(n+P)
      * ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s)
      (𝓝[≠] (p k)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with s; rw [hrel s]; ring
  have hfun : (fun s : ℂ => (s - p k)^(n+P)
      * ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s)
      = fun s : ℂ => ∑ j ∈ range (n+1),
          (c j).eval s * ((s - p k)^(n-j) * ((s - p k)^(j+P) * iteratedDeriv j f s)) := by
    funext s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [mem_range, Nat.lt_succ_iff] at hj
    rw [← mul_assoc ((s - p k)^(n-j)), ← pow_add, show (n-j)+(j+P) = n+P by omega]
    ring
  have hterms : Tendsto (fun s : ℂ => ∑ j ∈ range (n+1),
      (c j).eval s * ((s - p k)^(n-j) * ((s - p k)^(j+P) * iteratedDeriv j f s)))
      (𝓝[≠] (p k))
      (𝓝 (∑ j ∈ range (n+1), (c j).eval (p k) * (((p k) - p k)^(n-j) * L j k))) := by
    apply tendsto_finsetSum
    intro j _
    have hcj : Tendsto (fun s : ℂ => (c j).eval s) (𝓝[≠] (p k)) (𝓝 ((c j).eval (p k))) :=
      (c j).continuous.continuousAt.continuousWithinAt
    have hpow : Tendsto (fun s : ℂ => (s - p k)^(n-j)) (𝓝[≠] (p k))
        (𝓝 (((p k) - p k)^(n-j))) :=
      ((continuous_id.sub continuous_const).pow (n-j)).continuousAt.continuousWithinAt
    exact hcj.mul (hpow.mul (hres j k))
  rw [hfun] at h0
  have hval : (∑ j ∈ range (n+1), (c j).eval (p k) * (((p k) - p k)^(n-j) * L j k))
      = (c n).eval (p k) * L n k := by
    rw [Finset.sum_eq_single n]
    · rw [sub_self, Nat.sub_self, pow_zero, one_mul]
    · intro j hjmem hjn
      rw [mem_range, Nat.lt_succ_iff] at hjmem
      have hnj : n - j ≠ 0 := by omega
      rw [sub_self, zero_pow hnj, zero_mul, mul_zero]
    · intro h; simp at h
  rw [hval] at hterms
  have := tendsto_nhds_unique h0 hterms
  rcases mul_eq_zero.mp this.symm with h | h
  · exact h
  · exact absurd h (hL n k)

/-- **The master pole-based not-holonomic criterion.**  A function whose `i`-th derivative has a pole of
order exactly `i+P` at every point of an injective sequence `p k`, with nonvanishing leading
coefficient, satisfies no linear differential equation with polynomial coefficients.  This subsumes all
the pole-based engines — `not_holonomic_of_residues` (`p k = −k`, `P = 1`) and
`not_holonomic_of_residues_order` (`p k = −k`) — and covers poles at any injective locations: shifted
Gamma, scaled Gamma, and functions poled off `−ℕ`. -/
theorem not_holonomic_master (f : ℂ → ℂ) (p : ℕ → ℂ) (hp : Function.Injective p) (P : ℕ)
    (L : ℕ → ℕ → ℂ) (hL : ∀ i k, L i k ≠ 0)
    (hres : ∀ i k : ℕ, Tendsto (fun s : ℂ => (s - p k)^(i+P) * iteratedDeriv i f s)
      (𝓝[≠] (p k)) (𝓝 (L i k))) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  intro n
  induction n with
  | zero =>
    intro c hrel j hj
    rw [mem_range, Nat.lt_one_iff] at hj; subst hj
    exact linear_top_zero_master f p hp P L hL hres 0 c hrel
  | succ m ih =>
    intro c hrel
    have htop : c (m+1) = 0 := linear_top_zero_master f p hp P L hL hres (m+1) c hrel
    have hrel' : ∀ s, ∑ j ∈ range (m+1), (c j).eval s * iteratedDeriv j f s = 0 := by
      intro s; have h := hrel s; rw [Finset.sum_range_succ, htop] at h
      simp only [Polynomial.eval_zero, zero_mul, add_zero] at h; exact h
    intro j hj; rw [mem_range, Nat.lt_succ_iff] at hj
    rcases eq_or_lt_of_le hj with hjm | hjm
    · rw [hjm]; exact htop
    · exact ih c hrel' j (mem_range.mpr (by omega))

/-- **The shifted Gamma function is not holonomic, for every complex shift.**  `s ↦ Γ(s+a)` satisfies no
linear ODE with polynomial coefficients: it has simple poles at the injective sequence `−a−k`, with
residues inherited from `gamma_iteratedDeriv_residue` via `iteratedDeriv_comp_add_const`.  A first
instance of `not_holonomic_master` at pole locations off `−ℕ`. -/
theorem shiftedGamma_not_holonomic (a : ℂ) : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun s => Complex.Gamma (s + a)) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  apply not_holonomic_master (fun s => Complex.Gamma (s + a)) (fun k => -a - (k:ℂ))
    (fun x y hxy => by
      have h : (x:ℂ) = (y:ℂ) := by linear_combination -hxy
      exact_mod_cast h) 1
    (fun i k => (-1)^i * (i.factorial:ℂ) * ((-1)^k / (k.factorial:ℂ)))
    (fun i k => mul_ne_zero (mul_ne_zero (pow_ne_zero i (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero i))
      (div_ne_zero (pow_ne_zero k (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)))
  intro i k
  have hcomp : ∀ s : ℂ, iteratedDeriv i (fun s => Complex.Gamma (s + a)) s
      = iteratedDeriv i Complex.Gamma (s + a) :=
    fun s => congrFun (iteratedDeriv_comp_add_const i Complex.Gamma a) s
  have hshift : Tendsto (fun s : ℂ => s + a) (𝓝[≠] (-a - (k:ℂ))) (𝓝[≠] (-(k:ℂ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℂ => s + a) (𝓝 (-a - (k:ℂ))) (𝓝 ((-a - (k:ℂ)) + a)) :=
        (continuous_id.add continuous_const).continuousAt
      rw [show (-a - (k:ℂ)) + a = -(k:ℂ) by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h; exact hs (by linear_combination h)
  have hg := (gamma_iteratedDeriv_residue i k).comp hshift
  simp_rw [hcomp]
  refine Tendsto.congr (fun s => ?_) hg
  simp only [Function.comp_apply]
  rw [show s - (-a - (k:ℂ)) = (s + a) + (k:ℂ) by ring]

/-- **The shifted polygamma family is not holonomic.**  For every order `M` and every complex shift
`a`, `s ↦ ψ⁽ᴹ⁾(s+a)` satisfies no linear ODE with polynomial coefficients — a two-parameter family
discharged in one theorem.  An instance of `not_holonomic_master` combining both its generalizations:
poles at the shifted locations `−a−k` (order `M+1`), with residues from `digamma_iteratedDeriv_residue`
transported through `iteratedDeriv_comp_add_const` and `iteratedDeriv_comp_iterate`. -/
theorem shiftedPolygamma_not_holonomic (M : ℕ) (a : ℂ) : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun s => iteratedDeriv M Complex.digamma (s + a)) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  apply not_holonomic_master (fun s => iteratedDeriv M Complex.digamma (s + a))
    (fun k => -a - (k:ℂ))
    (fun x y hxy => by
      have h : (x:ℂ) = (y:ℂ) := by linear_combination -hxy
      exact_mod_cast h) (M+1)
    (fun i k => (-1)^(i+M+1) * ((i+M).factorial : ℂ))
    (fun i k => mul_ne_zero (pow_ne_zero (i+M+1) (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero (i+M)))
  intro i k
  have hcomp : ∀ s : ℂ, iteratedDeriv i (fun s => iteratedDeriv M Complex.digamma (s + a)) s
      = iteratedDeriv (i + M) Complex.digamma (s + a) := by
    intro s
    rw [congrFun (iteratedDeriv_comp_add_const i (iteratedDeriv M Complex.digamma) a) s,
        iteratedDeriv_comp_iterate]
  have hshift : Tendsto (fun s : ℂ => s + a) (𝓝[≠] (-a - (k:ℂ))) (𝓝[≠] (-(k:ℂ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℂ => s + a) (𝓝 (-a - (k:ℂ))) (𝓝 ((-a - (k:ℂ)) + a)) :=
        (continuous_id.add continuous_const).continuousAt
      rw [show (-a - (k:ℂ)) + a = -(k:ℂ) by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h; exact hs (by linear_combination h)
  have hg := (digamma_iteratedDeriv_residue (i + M) k).comp hshift
  simp_rw [hcomp]
  refine Tendsto.congr (fun s => ?_) hg
  simp only [Function.comp_apply]
  rw [show s - (-a - (k:ℂ)) = (s + a) + (k:ℂ) by ring, show i + (M + 1) = (i + M) + 1 by omega]

/-- **The sine has a simple zero at 0:** `sin w = w·g(w)` near `0` with `g` analytic and `g(0)=1`.  From
the general analytic-zero factorization, with order `1` forced by `sin'(0)=cos(0)=1 ≠ 0`. -/
theorem sin_factor : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 1 ∧
    ∀ᶠ w in 𝓝 (0:ℂ), Complex.sin w = w * g w := by
  have hderiv1 : HasDerivAt Complex.sin 1 0 := by simpa using Complex.hasDerivAt_sin 0
  have hnz : ¬ ∀ᶠ w in 𝓝 (0:ℂ), Complex.sin w = 0 := by
    intro h
    have h' : Complex.sin =ᶠ[𝓝 (0:ℂ)] fun _ => (0:ℂ) := h
    exact one_ne_zero (hderiv1.unique (h'.hasDerivAt_iff.mpr (hasDerivAt_const 0 0)))
  obtain ⟨n, g, hg, hgne, hfac⟩ := analyticAt_sin.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  simp only [sub_zero] at hfac
  have hn1 : n = 1 := by
    rcases n with _ | _ | m
    · exfalso
      have hs := hfac.self_of_nhds
      simp only [pow_zero, one_smul, Complex.sin_zero] at hs
      exact hgne hs.symm
    · rfl
    · exfalso
      have hp : HasDerivAt (fun w : ℂ => w ^ (m+2)) 0 0 := by
        simpa [zero_pow (Nat.succ_ne_zero m)] using hasDerivAt_pow (m+2) (0:ℂ)
      have hd : HasDerivAt (fun w : ℂ => w ^ (m+2) • g w) 0 0 := by
        have hfun :
            (fun w : ℂ => w ^ (m + 2) • g w) = (fun w : ℂ => w ^ (m + 2)) • g := by
          funext w
          rfl
        rw [hfun]
        simpa only [Pi.smul_apply, zero_pow (show m + 2 ≠ 0 by omega), zero_smul, add_zero] using
          hp.smul (hg.differentiableAt.hasDerivAt)
      have hfac' : Complex.sin =ᶠ[𝓝 (0:ℂ)] fun w => w ^ (m+2) • g w := hfac
      exact one_ne_zero (hderiv1.unique (hfac'.hasDerivAt_iff.mpr hd))
  subst hn1
  simp only [pow_one] at hfac
  have hfacm : Complex.sin =ᶠ[𝓝 (0:ℂ)] fun w => w * g w := by
    filter_upwards [hfac] with w hw; simpa using hw
  refine ⟨g, hg, ?_, hfacm⟩
  have hd : HasDerivAt (fun w : ℂ => w * g w) (g 0) 0 := by
    have hfun : (fun w : ℂ => w * g w) = id * g := by
      funext w
      rfl
    rw [hfun]
    simpa only [one_mul, id_eq, zero_mul, add_zero] using
      (hasDerivAt_id (0 : ℂ)).mul (hg.differentiableAt.hasDerivAt)
  exact (hderiv1.unique (hfacm.hasDerivAt_iff.mpr hd)).symm

/-- **Reflection of sine across an integer multiple of π:** `sin s = (−1)^n·sin(s − nπ)`. -/
theorem sin_reflect (n : ℕ) (s : ℂ) :
    Complex.sin s = (-1) ^ n * Complex.sin (s - ↑n * ↑Real.pi) := by
  have hcos : Complex.cos (↑n * ↑Real.pi) = (-1) ^ n := by
    rw [show (↑n * ↑Real.pi : ℂ) = (((n : ℤ) * Real.pi : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cos, Real.cos_int_mul_pi, zpow_natCast]
    push_cast; ring
  have key : Complex.sin s = Complex.sin ((s - ↑n * ↑Real.pi) + ↑n * ↑Real.pi) := by congr 1; ring
  rw [key, Complex.sin_add, Complex.sin_nat_mul_pi, hcos]; ring

/-- **Derivative residues from a simple-pole factorization at `−c`.**  The additive-constant form of
`iteratedDeriv_residue_of_factor` (pole at `−c` for arbitrary `c : ℂ`, not only `c = k`): if
`f = G·(t+c)⁻¹` on an open set approaching `−c` with `G` smooth there and at `−c`, then
`(s+c)^{j+1}·f⁽ʲ⁾(s) → G(−c)·(−1)^j·j!`.  Feeds `not_holonomic_master` for functions poled off `−ℕ`. -/
theorem iteratedDeriv_residue_of_factor_add (f G : ℂ → ℂ) (c : ℂ) (U : Set ℂ)
    (hkne : ∀ s ∈ U, s + c ≠ 0)
    (hUnhds : ∀ᶠ s in 𝓝[≠] (-c), s ∈ U)
    (hGU : ∀ s ∈ U, ∀ n : ℕ, ContDiffAt ℂ n G s)
    (hGk : ∀ n : ℕ, ContDiffAt ℂ n G (-c))
    (hfac : ∀ s ∈ U, f =ᶠ[𝓝 s] G * fun t : ℂ => (t + c)⁻¹)
    (j : ℕ) :
    Tendsto (fun s : ℂ => (s + c)^(j+1) * iteratedDeriv j f s) (𝓝[≠] (-c))
      (𝓝 (G (-c) * ((-1)^j * (j.factorial:ℂ)))) := by
  have hev : ∀ᶠ s in 𝓝[≠] (-c),
      (s + c)^(j+1) * iteratedDeriv j f s = ∑ i ∈ range (j+1),
        (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ))) * (s + c)^i := by
    filter_upwards [hUnhds] with s hsU
    have hk0 : s + c ≠ 0 := hkne s hsU
    have hcdInv : ContDiffAt ℂ j (fun t => (t + c)⁻¹) s :=
      (by fun_prop : ContDiffAt ℂ j (fun t : ℂ => t + c) s).inv hk0
    rw [(hfac s hsU).iteratedDeriv_eq, iteratedDeriv_mul (𝕜 := ℂ) (hGU s hsU j) hcdInv, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mem_range, Nat.lt_succ_iff] at hi
    rw [iteratedDeriv_inv_add_const c (j-i) s hk0]
    have hpow : (s + c)^(j+1) * ((s + c)^((j-i)+1))⁻¹ = (s + c)^i := by
      rw [← pow_sub₀ _ hk0 (by omega : (j-i)+1 ≤ j+1)]; congr 1; omega
    linear_combination ((j.choose i : ℂ) * iteratedDeriv i G s * (-1)^(j-i)
      * ((j-i).factorial : ℂ)) * hpow
  have hlim : Tendsto (fun s : ℂ => ∑ i ∈ range (j+1),
      (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ))) * (s + c)^i)
      (𝓝[≠] (-c)) (𝓝 (G (-c) * ((-1)^j * (j.factorial:ℂ)))) := by
    have hterms : Tendsto (fun s : ℂ => ∑ i ∈ range (j+1),
        (j.choose i : ℂ) * (iteratedDeriv i G s * ((-1)^(j-i) * ((j-i).factorial : ℂ))) * (s + c)^i)
        (𝓝[≠] (-c)) (𝓝 (∑ i ∈ range (j+1),
          (j.choose i : ℂ) * (iteratedDeriv i G (-c) * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
            * ((-c) + c)^i)) := by
      apply tendsto_finsetSum
      intro i _
      exact ((tendsto_const_nhds).mul
        ((continuousAt_iteratedDeriv_of_contDiffAt (hGk i)).continuousWithinAt.mul tendsto_const_nhds)).mul
        (((continuous_id.add continuous_const).pow i).continuousAt.continuousWithinAt)
    have hval : (∑ i ∈ range (j+1),
        (j.choose i : ℂ) * (iteratedDeriv i G (-c) * ((-1)^(j-i) * ((j-i).factorial : ℂ)))
          * ((-c) + c)^i) = G (-c) * ((-1)^j * (j.factorial:ℂ)) := by
      rw [Finset.sum_eq_single 0]
      · simp only [pow_zero, mul_one, iteratedDeriv_zero, Nat.choose_zero_right, Nat.cast_one,
          one_mul, Nat.sub_zero]
      · intro i _ hi0; rw [neg_add_cancel, zero_pow hi0, mul_zero]
      · intro h; simp at h
    rw [hval] at hterms; exact hterms
  exact hlim.congr' (hev.mono (fun _ h => h.symm))

/-- **The cosecant `csc = 1/sin` is not holonomic.**  It satisfies no linear ODE with polynomial
coefficients — the first *trigonometric* (non-Gamma) instance of `not_holonomic_master`.  `csc` has a
simple pole at every `nπ` (`n : ℕ`), with analytic extension `G(s) = (−1)^n/g(s−nπ)` (value `(−1)^n`)
built from `sin_factor` and `sin_reflect`; its derivative residues come from
`iteratedDeriv_residue_of_factor_add`. -/
theorem csc_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun s => (Complex.sin s)⁻¹) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  obtain ⟨g, hg, hg0, hgfac⟩ := sin_factor
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (show {w : ℂ | Complex.sin w = w * g w ∧ g w ≠ 0 ∧ ∀ m : ℕ, ContDiffAt ℂ m g w} ∈ 𝓝 (0:ℂ) by
      filter_upwards [hgfac, hg.continuousAt.eventually_ne (by rw [hg0]; exact one_ne_zero),
        hg.eventually_analyticAt] with w h1 h2 h3
      exact ⟨h1, h2, fun m => h3.contDiffAt⟩)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply not_holonomic_master (fun s => (Complex.sin s)⁻¹) (fun m => (m : ℂ) * (Real.pi : ℂ))
    (fun x y hxy => by
      have : (x : ℂ) = y := by
        have := mul_right_cancel₀ hpi hxy; exact this
      exact_mod_cast this) 1
    (fun i m => (-1)^m * ((-1)^i * (i.factorial : ℂ)))
    (fun i m => mul_ne_zero (pow_ne_zero m (by norm_num))
      (mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero i)))
  intro i m
  set z₀ : ℂ := (m : ℂ) * (Real.pi : ℂ) with hz₀
  set Gc : ℂ → ℂ := fun s => (-1)^m / g (s - z₀) with hGc
  have hGcval : Gc z₀ = (-1)^m := by
    simp only [hGc, sub_self]; rw [hg0]; ring
  have hUsub : Metric.ball z₀ r \ {z₀} ⊆ {s | Complex.sin s = (-1)^m * ((s - z₀) * g (s - z₀))
      ∧ g (s - z₀) ≠ 0 ∧ (∀ mm : ℕ, ContDiffAt ℂ mm g (s - z₀)) ∧ s ≠ z₀} := by
    intro s hs
    have hwin : (s - z₀) ∈ Metric.ball (0:ℂ) r := by
      have hs1 : s ∈ Metric.ball z₀ r := hs.1
      rw [Metric.mem_ball, Complex.dist_eq] at hs1
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; exact hs1
    obtain ⟨hsin, hgne, hcd⟩ := hrsub hwin
    refine ⟨?_, hgne, hcd, ?_⟩
    · rw [sin_reflect m s, ← hz₀, hsin]
    · exact fun h => hs.2 (by rw [Set.mem_singleton_iff]; exact h)
  have key := iteratedDeriv_residue_of_factor_add (fun s => (Complex.sin s)⁻¹) Gc (-z₀)
    (Metric.ball z₀ r \ {z₀})
    (fun s hs => by
      have hne := (hUsub hs).2.2.2; intro h; exact hne (by linear_combination h))
    (by
      rw [neg_neg]
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds z₀ hr),
        self_mem_nhdsWithin] with s hb hne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
      exact ⟨hb, hne⟩)
    (fun s hs mm => by
      simp only [hGc]
      exact (contDiffAt_const).div (((hUsub hs).2.2.1 mm).comp s (by fun_prop)) (hUsub hs).2.1)
    (by
      rw [neg_neg]
      intro mm
      simp only [hGc]
      have hgc : ContDiffAt ℂ mm g (z₀ - z₀) := by rw [sub_self]; exact hg.contDiffAt
      exact (contDiffAt_const).div
        (ContDiffAt.comp (f := fun s : ℂ => s - z₀) z₀ hgc (by fun_prop))
        (by simp [sub_self, hg0]))
    (fun s hs => by
      have hfacts := hUsub hs
      refine Filter.eventuallyEq_of_mem
        ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hs) (fun t ht => ?_)
      have hft := hUsub ht
      show (Complex.sin t)⁻¹ = Gc t * (t + -z₀)⁻¹
      simp only [hGc]
      have hsq : ((-1:ℂ))^m * ((-1:ℂ))^m = 1 := by rw [← mul_pow]; norm_num
      rw [hft.1, show t + -z₀ = t - z₀ from by ring, mul_inv, mul_inv, div_eq_mul_inv,
        inv_eq_of_mul_eq_one_right hsq]
      ring) i
  rw [neg_neg, hGcval] at key
  refine key.congr' ?_
  filter_upwards with s
  rw [show s + -z₀ = s - z₀ by ring]

/-- `cos(nπ) = (−1)^n`. -/
theorem cos_nat_pi (m : ℕ) : Complex.cos (↑m * ↑Real.pi) = (-1) ^ m := by
  rw [show (↑m * ↑Real.pi : ℂ) = (((m : ℤ) * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_int_mul_pi, zpow_natCast]
  push_cast; ring

/-- **The cotangent `cot = cos/sin` is not holonomic.**  It satisfies no linear ODE with polynomial
coefficients — a second trigonometric instance of `not_holonomic_master`, sharing csc's simple poles at
`nπ` but with residue `1` (extension `G(s) = cos(s)·(−1)^n/g(s−nπ)`, value `cos(nπ)·(−1)^n = 1`). -/
theorem cot_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun s => Complex.cos s / Complex.sin s) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  obtain ⟨g, hg, hg0, hgfac⟩ := sin_factor
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (show {w : ℂ | Complex.sin w = w * g w ∧ g w ≠ 0 ∧ ∀ m : ℕ, ContDiffAt ℂ m g w} ∈ 𝓝 (0:ℂ) by
      filter_upwards [hgfac, hg.continuousAt.eventually_ne (by rw [hg0]; exact one_ne_zero),
        hg.eventually_analyticAt] with w h1 h2 h3
      exact ⟨h1, h2, fun m => h3.contDiffAt⟩)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply not_holonomic_master (fun s => Complex.cos s / Complex.sin s) (fun m => (m : ℂ) * (Real.pi : ℂ))
    (fun x y hxy => by
      have : (x : ℂ) = y := mul_right_cancel₀ hpi hxy
      exact_mod_cast this) 1
    (fun i m => (-1)^i * (i.factorial : ℂ))
    (fun i m => mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero i))
  intro i m
  set z₀ : ℂ := (m : ℂ) * (Real.pi : ℂ) with hz₀
  set Gc : ℂ → ℂ := fun s => Complex.cos s * ((-1)^m / g (s - z₀)) with hGc
  have hcosval : Complex.cos z₀ = (-1)^m := by rw [hz₀]; exact cos_nat_pi m
  have hsq : ((-1:ℂ))^m * ((-1:ℂ))^m = 1 := by rw [← mul_pow]; norm_num
  have hGcval : Gc z₀ = 1 := by
    simp only [hGc, sub_self]; rw [hg0, hcosval, div_one]; exact hsq
  have hUsub : Metric.ball z₀ r \ {z₀} ⊆ {s | Complex.sin s = (-1)^m * ((s - z₀) * g (s - z₀))
      ∧ g (s - z₀) ≠ 0 ∧ (∀ mm : ℕ, ContDiffAt ℂ mm g (s - z₀)) ∧ s ≠ z₀} := by
    intro s hs
    have hwin : (s - z₀) ∈ Metric.ball (0:ℂ) r := by
      have hs1 : s ∈ Metric.ball z₀ r := hs.1
      rw [Metric.mem_ball, Complex.dist_eq] at hs1
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; exact hs1
    obtain ⟨hsin, hgne, hcd⟩ := hrsub hwin
    refine ⟨?_, hgne, hcd, fun h => hs.2 (by rw [Set.mem_singleton_iff]; exact h)⟩
    rw [sin_reflect m s, ← hz₀, hsin]
  have key := iteratedDeriv_residue_of_factor_add (fun s => Complex.cos s / Complex.sin s) Gc (-z₀)
    (Metric.ball z₀ r \ {z₀})
    (fun s hs => by
      have hne := (hUsub hs).2.2.2; intro h; exact hne (by linear_combination h))
    (by
      rw [neg_neg]
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds z₀ hr),
        self_mem_nhdsWithin] with s hb hne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
      exact ⟨hb, hne⟩)
    (fun s hs mm => by
      simp only [hGc]
      exact ContDiffAt.mul (by fun_prop)
        ((contDiffAt_const).div (((hUsub hs).2.2.1 mm).comp s (by fun_prop)) (hUsub hs).2.1))
    (by
      rw [neg_neg]; intro mm; simp only [hGc]
      have hgc : ContDiffAt ℂ mm g (z₀ - z₀) := by rw [sub_self]; exact hg.contDiffAt
      exact ContDiffAt.mul (by fun_prop) ((contDiffAt_const).div
        (ContDiffAt.comp (f := fun s : ℂ => s - z₀) z₀ hgc (by fun_prop))
        (by rw [sub_self, hg0]; exact one_ne_zero)))
    (fun s hs => by
      refine Filter.eventuallyEq_of_mem
        ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hs) (fun t ht => ?_)
      have hft := hUsub ht
      show Complex.cos t / Complex.sin t = Gc t * (t + -z₀)⁻¹
      simp only [hGc]
      rw [hft.1, show t + -z₀ = t - z₀ from by ring]
      simp only [div_eq_mul_inv, mul_inv, inv_eq_of_mul_eq_one_right hsq]
      ring) i
  rw [neg_neg, hGcval, one_mul] at key
  exact key

/-- **Reflection of cosine across `nπ+π/2`:** `cos s = (−1)^{n+1}·sin(s − (nπ+π/2))` — cosine's zeros
mirror sine's, so the `sin` simple-zero factorization drives the poles of `sec`/`tan`. -/
theorem cos_half_reflect (n : ℕ) (s : ℂ) :
    Complex.cos s = (-1)^(n+1) * Complex.sin (s - (↑n * ↑Real.pi + ↑Real.pi / 2)) := by
  have hcosp : Complex.cos (↑n * ↑Real.pi + ↑Real.pi / 2) = 0 := by
    rw [Complex.cos_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two, Complex.sin_nat_mul_pi]; ring
  have hsinp : Complex.sin (↑n * ↑Real.pi + ↑Real.pi / 2) = (-1)^n := by
    rw [Complex.sin_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two, Complex.sin_nat_mul_pi,
        cos_nat_pi]; ring
  have key : Complex.cos s
      = Complex.cos ((s - (↑n * ↑Real.pi + ↑Real.pi / 2)) + (↑n * ↑Real.pi + ↑Real.pi / 2)) := by
    congr 1; ring
  rw [key, Complex.cos_add, hcosp, hsinp]; ring

/-- **No entire numerator over cosine is holonomic.**  If `N` is smooth on `ℂ` and nonzero at every
zero `mπ + π/2` of `cos`, then `N / cos` satisfies no linear differential equation with polynomial
coefficients.  At each such point the quotient has a simple pole with residue
`N(mπ + π/2) · (-1)^(m+1)`, so the `i`th derivative blows up like `(-1)^i i!` times that residue —
a family of nonzero residues at infinitely many points, which `not_holonomic_master` turns into
vanishing of every coefficient. -/
theorem div_cos_not_holonomic (N : ℂ → ℂ) (hN : ∀ (s : ℂ) (m : ℕ), ContDiffAt ℂ m N s)
    (hNz : ∀ m : ℕ, N ((m : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 2) ≠ 0) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun s => N s / Complex.cos s) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by

  obtain ⟨g, hg, hg0, hgfac⟩ := sin_factor
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (show {w : ℂ | Complex.sin w = w * g w ∧ g w ≠ 0 ∧ ∀ m : ℕ, ContDiffAt ℂ m g w} ∈ 𝓝 (0:ℂ) by
      filter_upwards [hgfac, hg.continuousAt.eventually_ne (by rw [hg0]; exact one_ne_zero),
        hg.eventually_analyticAt] with w h1 h2 h3
      exact ⟨h1, h2, fun m => h3.contDiffAt⟩)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply not_holonomic_master (fun s => N s / Complex.cos s)
    (fun m => (m : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 2)
    (fun x y hxy => by
      have hx2 : (x : ℂ) * Real.pi = (y : ℂ) * Real.pi := by linear_combination hxy
      have : (x : ℂ) = y := mul_right_cancel₀ hpi hx2
      exact_mod_cast this) 1
    (fun i m => N ((m : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 2) * (-1)^(m+1) *
      ((-1)^i * (i.factorial : ℂ)))
    (fun i m => mul_ne_zero (mul_ne_zero (hNz m) (pow_ne_zero (m+1) (by norm_num)))
      (mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero i)))
  intro i m
  set z₀ : ℂ := (m : ℂ) * (Real.pi : ℂ) + (Real.pi : ℂ) / 2 with hz₀
  set Gc : ℂ → ℂ := fun s => N s * ((-1)^(m+1) / g (s - z₀)) with hGc
  have hsqi : ((-1:ℂ))^(m+1) * ((-1:ℂ))^(m+1) = 1 := by rw [← mul_pow]; norm_num
  have hGcval : Gc z₀ = N z₀ * (-1)^(m+1) := by
    simp only [hGc, sub_self]; rw [hg0, div_one]
  have hUsub : Metric.ball z₀ r \ {z₀} ⊆ {s | Complex.cos s = (-1)^(m+1) * ((s - z₀) * g (s - z₀))
      ∧ g (s - z₀) ≠ 0 ∧ (∀ mm : ℕ, ContDiffAt ℂ mm g (s - z₀)) ∧ s ≠ z₀} := by
    intro s hs
    have hwin : (s - z₀) ∈ Metric.ball (0:ℂ) r := by
      have hs1 : s ∈ Metric.ball z₀ r := hs.1
      rw [Metric.mem_ball, Complex.dist_eq] at hs1
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; exact hs1
    obtain ⟨hsin, hgne, hcd⟩ := hrsub hwin
    refine ⟨?_, hgne, hcd, fun h => hs.2 (by rw [Set.mem_singleton_iff]; exact h)⟩
    rw [cos_half_reflect m s, ← hz₀, hsin]
  have key := iteratedDeriv_residue_of_factor_add (fun s => N s / Complex.cos s) Gc (-z₀)
    (Metric.ball z₀ r \ {z₀})
    (fun s hs => by
      have hne := (hUsub hs).2.2.2; intro h; exact hne (by linear_combination h))
    (by
      rw [neg_neg]
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds z₀ hr),
        self_mem_nhdsWithin] with s hb hne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
      exact ⟨hb, hne⟩)
    (fun s hs mm => by
      simp only [hGc]
      exact ContDiffAt.mul (hN s mm)
        ((contDiffAt_const).div (((hUsub hs).2.2.1 mm).comp s (by fun_prop)) (hUsub hs).2.1))
    (by
      rw [neg_neg]; intro mm; simp only [hGc]
      have hgc : ContDiffAt ℂ mm g (z₀ - z₀) := by rw [sub_self]; exact hg.contDiffAt
      exact ContDiffAt.mul (hN z₀ mm) ((contDiffAt_const).div
        (ContDiffAt.comp (f := fun s : ℂ => s - z₀) z₀ hgc (by fun_prop))
        (by rw [sub_self, hg0]; exact one_ne_zero)))
    (fun s hs => by
      refine Filter.eventuallyEq_of_mem
        ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hs) (fun t ht => ?_)
      have hft := hUsub ht
      show N t / Complex.cos t = Gc t * (t + -z₀)⁻¹
      simp only [hGc]
      rw [hft.1, show t + -z₀ = t - z₀ from by ring]
      simp only [div_eq_mul_inv, mul_inv, inv_eq_of_mul_eq_one_right hsqi]
      ring) i
  rw [neg_neg, hGcval] at key
  refine key.congr' ?_
  filter_upwards with s
  rw [show s + -z₀ = s - z₀ by ring]

/-- **The tangent `tan = sin/cos` is not holonomic.**  It satisfies no linear ODE with polynomial
coefficients — a trigonometric instance of `not_holonomic_master` with poles at `nπ+π/2` (cosine's
zeros).  Extension `G(s) = sin(s)·(−1)^{n+1}/g(s−(nπ+π/2))` of value `sin(nπ+π/2)·(−1)^{n+1} = −1`,
using `cos_half_reflect` to reduce cosine's zero to sine's (`sin_factor`). -/
theorem tan_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun s => Complex.sin s / Complex.cos s) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  have h := div_cos_not_holonomic Complex.sin (fun s m => by fun_prop) (fun m => ?_)
  · exact h
  · rw [Complex.sin_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two,
      Complex.sin_nat_mul_pi, cos_nat_pi]
    simp

/-- **The secant `sec = 1/cos` is not holonomic.**  It satisfies no linear ODE with polynomial
coefficients — the `csc`-analogue for cosine: simple poles at `nπ+π/2` (`cos_half_reflect`), extension
`G(s) = (−1)^{m+1}/g(s−(nπ+π/2))` of value `(−1)^{m+1}`.  Completes `csc, cot, tan, sec`. -/
theorem sec_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun s => (Complex.cos s)⁻¹) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  have h := div_cos_not_holonomic (fun _ => (1 : ℂ))
    (fun _ _ => contDiffAt_const) (fun _ => one_ne_zero)
  simpa only [one_div] using h

/-- **The hyperbolic sine has a simple zero at 0:** `sinh w = w·g(w)` near `0` with `g` analytic,
`g(0)=1` (order `1` forced by `sinh'(0)=cosh(0)=1`).  The hyperbolic analogue of `sin_factor`. -/
theorem sinh_factor : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 1 ∧
    ∀ᶠ w in 𝓝 (0:ℂ), Complex.sinh w = w * g w := by
  have hana : AnalyticAt ℂ Complex.sinh 0 := Complex.analyticAt_sinh
  have hderiv1 : HasDerivAt Complex.sinh 1 0 := by simpa using Complex.hasDerivAt_sinh 0
  have hnz : ¬ ∀ᶠ w in 𝓝 (0:ℂ), Complex.sinh w = 0 := by
    intro h
    have h' : Complex.sinh =ᶠ[𝓝 (0:ℂ)] fun _ => (0:ℂ) := h
    exact one_ne_zero (hderiv1.unique (h'.hasDerivAt_iff.mpr (hasDerivAt_const 0 0)))
  obtain ⟨n, g, hg, hgne, hfac⟩ := hana.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  simp only [sub_zero] at hfac
  have hn1 : n = 1 := by
    rcases n with _ | _ | mm
    · exfalso
      have hs := hfac.self_of_nhds
      simp only [pow_zero, one_smul, Complex.sinh_zero] at hs
      exact hgne hs.symm
    · rfl
    · exfalso
      have hp : HasDerivAt (fun w : ℂ => w ^ (mm+2)) 0 0 := by
        simpa [zero_pow (Nat.succ_ne_zero mm)] using hasDerivAt_pow (mm+2) (0:ℂ)
      have hd : HasDerivAt (fun w : ℂ => w ^ (mm+2) • g w) 0 0 := by
        have hfun :
            (fun w : ℂ => w ^ (mm + 2) • g w) = (fun w : ℂ => w ^ (mm + 2)) • g := by
          funext w
          rfl
        rw [hfun]
        simpa only [Pi.smul_apply, zero_pow (show mm + 2 ≠ 0 by omega), zero_smul, add_zero] using
          hp.smul (hg.differentiableAt.hasDerivAt)
      have hfac' : Complex.sinh =ᶠ[𝓝 (0:ℂ)] fun w => w ^ (mm+2) • g w := hfac
      exact one_ne_zero (hderiv1.unique (hfac'.hasDerivAt_iff.mpr hd))
  subst hn1
  simp only [pow_one] at hfac
  have hfacm : Complex.sinh =ᶠ[𝓝 (0:ℂ)] fun w => w * g w := by
    filter_upwards [hfac] with w hw; simpa using hw
  refine ⟨g, hg, ?_, hfacm⟩
  have hd : HasDerivAt (fun w : ℂ => w * g w) (g 0) 0 := by
    have hfun : (fun w : ℂ => w * g w) = id * g := by
      funext w
      rfl
    rw [hfun]
    simpa only [one_mul, id_eq, zero_mul, add_zero] using
      (hasDerivAt_id (0 : ℂ)).mul (hg.differentiableAt.hasDerivAt)
  exact (hderiv1.unique (hfacm.hasDerivAt_iff.mpr hd)).symm

/-- **Reflection of `sinh` across `inπ`:** `sinh s = (−1)^n·sinh(s − inπ)`, from `sinh(inπ)=0`,
`cosh(inπ)=(−1)^n` (via `sinh_mul_I`, `cosh_mul_I`). -/
theorem sinh_reflect (n : ℕ) (s : ℂ) :
    Complex.sinh s = (-1)^n * Complex.sinh (s - ↑n * ↑Real.pi * Complex.I) := by
  have hsinh0 : Complex.sinh (↑n * ↑Real.pi * Complex.I) = 0 := by
    rw [Complex.sinh_mul_I]; simp [Complex.sin_nat_mul_pi]
  have hcosh : Complex.cosh (↑n * ↑Real.pi * Complex.I) = (-1)^n := by
    rw [Complex.cosh_mul_I, cos_nat_pi]
  have key : Complex.sinh s
      = Complex.sinh ((s - ↑n * ↑Real.pi * Complex.I) + ↑n * ↑Real.pi * Complex.I) := by
    congr 1; ring
  rw [key, Complex.sinh_add, hsinh0, hcosh]; ring

/-- **The hyperbolic cosecant `csch = 1/sinh` is not holonomic.**  It satisfies no linear ODE with
polynomial coefficients — an instance of `not_holonomic_master` with poles on the **imaginary axis** at
`inπ` (not the real line), extension `G(s) = (−1)^m/g(s−inπ)` of value `(−1)^m`.  Shows the pole-based
criterion is oblivious to pole geometry: real (`−ℕ`, `nπ`) or imaginary (`inπ`). -/
theorem csch_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun s => (Complex.sinh s)⁻¹) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  obtain ⟨g, hg, hg0, hgfac⟩ := sinh_factor
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (show {w : ℂ | Complex.sinh w = w * g w ∧ g w ≠ 0 ∧ ∀ m : ℕ, ContDiffAt ℂ m g w} ∈ 𝓝 (0:ℂ) by
      filter_upwards [hgfac, hg.continuousAt.eventually_ne (by rw [hg0]; exact one_ne_zero),
        hg.eventually_analyticAt] with w h1 h2 h3
      exact ⟨h1, h2, fun m => h3.contDiffAt⟩)
  have hpiI : (↑Real.pi * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  apply not_holonomic_master (fun s => (Complex.sinh s)⁻¹) (fun m => (m : ℂ) * (↑Real.pi * Complex.I))
    (fun x y hxy => by
      have : (x : ℂ) = y := mul_right_cancel₀ hpiI hxy
      exact_mod_cast this) 1
    (fun i m => (-1)^m * ((-1)^i * (i.factorial : ℂ)))
    (fun i m => mul_ne_zero (pow_ne_zero m (by norm_num))
      (mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero i)))
  intro i m
  set z₀ : ℂ := (m : ℂ) * (↑Real.pi * Complex.I) with hz₀
  set Gc : ℂ → ℂ := fun s => (-1)^m / g (s - z₀) with hGc
  have hsq : ((-1:ℂ))^m * ((-1:ℂ))^m = 1 := by rw [← mul_pow]; norm_num
  have hGcval : Gc z₀ = (-1)^m := by simp only [hGc, sub_self]; rw [hg0, div_one]
  have hzeq : z₀ = ↑m * ↑Real.pi * Complex.I := by rw [hz₀]; ring
  have hUsub : Metric.ball z₀ r \ {z₀} ⊆ {s | Complex.sinh s = (-1)^m * ((s - z₀) * g (s - z₀))
      ∧ g (s - z₀) ≠ 0 ∧ (∀ mm : ℕ, ContDiffAt ℂ mm g (s - z₀)) ∧ s ≠ z₀} := by
    intro s hs
    have hwin : (s - z₀) ∈ Metric.ball (0:ℂ) r := by
      have hs1 : s ∈ Metric.ball z₀ r := hs.1
      rw [Metric.mem_ball, Complex.dist_eq] at hs1
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; exact hs1
    obtain ⟨hsin, hgne, hcd⟩ := hrsub hwin
    refine ⟨?_, hgne, hcd, fun h => hs.2 (by rw [Set.mem_singleton_iff]; exact h)⟩
    rw [sinh_reflect m s, ← hzeq, hsin]
  have key := iteratedDeriv_residue_of_factor_add (fun s => (Complex.sinh s)⁻¹) Gc (-z₀)
    (Metric.ball z₀ r \ {z₀})
    (fun s hs => by
      have hne := (hUsub hs).2.2.2; intro h; exact hne (by linear_combination h))
    (by
      rw [neg_neg]
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds z₀ hr),
        self_mem_nhdsWithin] with s hb hne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
      exact ⟨hb, hne⟩)
    (fun s hs mm => by
      simp only [hGc]
      exact (contDiffAt_const).div (((hUsub hs).2.2.1 mm).comp s (by fun_prop)) (hUsub hs).2.1)
    (by
      rw [neg_neg]; intro mm; simp only [hGc]
      have hgc : ContDiffAt ℂ mm g (z₀ - z₀) := by rw [sub_self]; exact hg.contDiffAt
      exact (contDiffAt_const).div
        (ContDiffAt.comp (f := fun s : ℂ => s - z₀) z₀ hgc (by fun_prop))
        (by rw [sub_self, hg0]; exact one_ne_zero))
    (fun s hs => by
      refine Filter.eventuallyEq_of_mem
        ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hs) (fun t ht => ?_)
      have hft := hUsub ht
      show (Complex.sinh t)⁻¹ = Gc t * (t + -z₀)⁻¹
      simp only [hGc]
      rw [hft.1, show t + -z₀ = t - z₀ from by ring]
      simp only [div_eq_mul_inv, mul_inv, inv_eq_of_mul_eq_one_right hsq]
      ring) i
  rw [neg_neg, hGcval] at key
  refine key.congr' ?_
  filter_upwards with s
  rw [show s + -z₀ = s - z₀ by ring]

/-- **Simple-pole lattice ⟹ not holonomic (the unifying criterion).**  If `f` factors as
`f = G_k·(s − p_k)⁻¹` on an open set approaching each point `p_k` of an injective sequence, with `G_k`
smooth there and at `p_k` and `G_k(p_k) ≠ 0` (i.e. `f` has a genuine simple pole with nonzero residue at
every `p_k`), then `f` satisfies no linear ODE with polynomial coefficients.  This packages
`iteratedDeriv_residue_of_factor_add` (residues) and `not_holonomic_master` (domination) into one
statement, and subsumes every instance in this development — `Γ`, `digamma`, the polygamma family,
shifted Gamma, `csc`, `cot`, `tan`, `sec`, `csch` — regardless of pole geometry (real `−ℕ`/`nπ` or
imaginary `inπ`). -/
theorem not_holonomic_of_simplePoles (f : ℂ → ℂ) (p : ℕ → ℂ) (hp : Function.Injective p)
    (G : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
    (hkne : ∀ k, ∀ s ∈ U k, s ≠ p k)
    (hUnhds : ∀ k, ∀ᶠ s in 𝓝[≠] (p k), s ∈ U k)
    (hGU : ∀ k, ∀ s ∈ U k, ∀ n : ℕ, ContDiffAt ℂ n (G k) s)
    (hGk : ∀ k, ∀ n : ℕ, ContDiffAt ℂ n (G k) (p k))
    (hGval : ∀ k, G k (p k) ≠ 0)
    (hfac : ∀ k, ∀ s ∈ U k, f =ᶠ[𝓝 s] G k * fun t : ℂ => (t - p k)⁻¹) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  apply not_holonomic_master f p hp 1
    (fun i k => G k (p k) * ((-1)^i * (i.factorial : ℂ)))
    (fun i k => mul_ne_zero (hGval k)
      (mul_ne_zero (pow_ne_zero i (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero i)))
  intro i k
  have key := iteratedDeriv_residue_of_factor_add f (G k) (-(p k)) (U k)
    (fun s hs h => hkne k s hs (by linear_combination h))
    (by rw [neg_neg]; exact hUnhds k)
    (hGU k)
    (by rw [neg_neg]; exact hGk k)
    (fun s hs => by
      have := hfac k s hs
      refine this.trans (Filter.EventuallyEq.rfl.mul ?_)
      filter_upwards with t
      rw [show t + -(p k) = t - p k from by ring])
    i
  rw [neg_neg] at key
  refine key.congr' ?_
  filter_upwards with s
  rw [show s + -(p k) = s - p k by ring]

/-- **Meromorphic with simple poles at a lattice ⟹ not holonomic (fully general criterion).**  If `f`
is `MeromorphicAt` each point `p_k` of an injective sequence with `meromorphicOrderAt f (p_k) = −1` (a
genuine simple pole), then `f` satisfies no linear ODE with polynomial coefficients.  The hypothesis is
now purely mathlib's meromorphic language — the analytic factorization `f = G_k·(s−p_k)⁻¹` is extracted
from `meromorphicOrderAt_eq_int_iff` and fed to `not_holonomic_of_simplePoles`.  Every not-holonomic
result in this development (`Γ`, `digamma`, polygamma, shifted Gamma, `csc/cot/tan/sec`, `csch`) is an
instance: each is meromorphic with simple poles at an injective lattice. -/
theorem not_holonomic_of_meromorphic_simplePoles (f : ℂ → ℂ) (p : ℕ → ℂ)
    (hp : Function.Injective p) (hmero : ∀ k, MeromorphicAt f (p k))
    (horder : ∀ k, meromorphicOrderAt f (p k) = ((-1 : ℤ) : WithTop ℤ)) :
    ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1), (c j).eval s * iteratedDeriv j f s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  have hext : ∀ k, ∃ (g : ℂ → ℂ) (ε : ℝ), 0 < ε ∧ (∀ m : ℕ, ContDiffAt ℂ m g (p k)) ∧ g (p k) ≠ 0 ∧
      (Metric.ball (p k) ε \ {p k}) ⊆
        {z | f z = (z - p k)⁻¹ * g z ∧ g z ≠ 0 ∧ ∀ m : ℕ, ContDiffAt ℂ m g z} := by
    intro k
    obtain ⟨g, hg, hgne, hfacptd⟩ := (meromorphicOrderAt_eq_int_iff (hmero k)).mp (horder k)
    have hfac' : f =ᶠ[𝓝[≠] (p k)] fun z => (z - p k)⁻¹ * g z := by
      filter_upwards [hfacptd] with z hz; rw [hz]; simp [zpow_neg, zpow_one]
    have hcomb : {z : ℂ | f z = (z - p k)⁻¹ * g z ∧ g z ≠ 0 ∧ ∀ m : ℕ, ContDiffAt ℂ m g z}
        ∈ 𝓝[≠] (p k) := by
      filter_upwards [hfac', nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hgne),
        nhdsWithin_le_nhds hg.eventually_analyticAt] with z h1 h2 h3
      exact ⟨h1, h2, fun m => h3.contDiffAt⟩
    rw [Metric.mem_nhdsWithin_iff] at hcomb
    obtain ⟨ε, hε, hsub⟩ := hcomb
    refine ⟨g, ε, hε, fun m => hg.contDiffAt, hgne, fun z hz => hsub ⟨hz.1, ?_⟩⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hz.2 (by rw [Set.mem_singleton_iff]; exact h)
  choose g ε hε hGk hgval hsub using hext
  apply not_holonomic_of_simplePoles f p hp g (fun k => Metric.ball (p k) (ε k) \ {p k})
    (fun k s hs h => hs.2 (by rw [Set.mem_singleton_iff]; exact h))
    (fun k => by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds (p k) (hε k)),
        self_mem_nhdsWithin] with s hb hne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
      exact ⟨hb, hne⟩)
    (fun k s hs m => (hsub k hs).2.2 m)
    hGk hgval
    (fun k s hs => by
      refine Filter.eventuallyEq_of_mem
        ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hs) (fun t ht => ?_)
      show f t = g k t * (t - p k)⁻¹
      rw [(hsub k ht).1]; ring)

/-- **The Bernoulli generating function `1/(eᶻ−1)` is not holonomic.**  It satisfies no linear ODE with
polynomial coefficients — a one-shot instance of `not_holonomic_of_meromorphic_simplePoles`, unrelated
to Γ or the trigonometric functions.  `eᶻ−1` is entire with a simple zero at each `2πik` (`eᶻ−1 = 0`,
derivative `eᶻ = 1 ≠ 0`), so its reciprocal has `meromorphicOrderAt = −1` at every `2πik`; the general
criterion does the rest.  The whole proof is establishing "meromorphic with a simple pole." -/
theorem bernoulliGF_not_holonomic : ∀ (n : ℕ) (c : ℕ → Polynomial ℂ),
    (∀ s : ℂ, ∑ j ∈ range (n+1),
      (c j).eval s * iteratedDeriv j (fun z => (Complex.exp z - 1)⁻¹) s = 0) →
    ∀ j ∈ range (n+1), c j = 0 := by
  apply not_holonomic_of_meromorphic_simplePoles (fun z => (Complex.exp z - 1)⁻¹)
    (fun k => (k : ℂ) * (2 * ↑Real.pi * Complex.I))
    (fun x y hxy => by
      have h2pi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      exact_mod_cast mul_right_cancel₀ h2pi hxy)
  · intro k
    apply MeromorphicAt.inv
    exact (analyticAt_cexp.sub analyticAt_const).meromorphicAt
  · intro k
    have hexp1 : Complex.exp ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) = 1 := by
      rw [show ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) = ((k : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    have hana : AnalyticAt ℂ (fun z => Complex.exp z - 1) ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) :=
      analyticAt_cexp.sub analyticAt_const
    have hzero : (fun z => Complex.exp z - 1) ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) = 0 := by
      simp only [hexp1, sub_self]
    have hderiv : deriv (fun z => Complex.exp z - 1) ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) ≠ 0 := by
      rw [((Complex.hasDerivAt_exp _).sub_const 1).deriv, hexp1]; exact one_ne_zero
    have hord1 : analyticOrderAt (fun z => Complex.exp z - 1) ((k : ℂ) * (2 * ↑Real.pi * Complex.I)) = 1 :=
      hana.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
    show meromorphicOrderAt ((fun z => Complex.exp z - 1)⁻¹) ((k : ℂ) * (2 * ↑Real.pi * Complex.I))
        = ((-1 : ℤ) : WithTop ℤ)
    rw [meromorphicOrderAt_inv, hana.meromorphicOrderAt_eq, hord1]
    rfl

/-- **Factorial beats any fixed power:** `kʲ/k! → 0` as `k → ∞`.  Ratio test (ratio `→ 0`). -/
theorem tendsto_natPow_div_factorial (j : ℕ) :
    Tendsto (fun k : ℕ => (k:ℝ)^j / k.factorial) atTop (𝓝 0) := by
  apply Summable.tendsto_atTop_zero
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have : (0:ℝ) < (k:ℝ)^j / k.factorial := by
      have : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      positivity
    exact ne_of_gt this
  · apply squeeze_zero' (g := fun k : ℕ => (2:ℝ)^j / ((k:ℝ)+1))
    · filter_upwards with k
      exact div_nonneg (norm_nonneg _) (norm_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with k hk
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
      have hfk : (0:ℝ) < (k:ℝ)^j / k.factorial := by positivity
      have hfk1 : (0:ℝ) < ((k:ℝ)+1)^j / ((k+1).factorial) := by positivity
      have hratio : ‖(fun k : ℕ => (k:ℝ)^j / k.factorial) (k+1)‖ /
          ‖(fun k : ℕ => (k:ℝ)^j / k.factorial) k‖ = ((k:ℝ)+1)^j / (((k:ℝ)+1) * (k:ℝ)^j) := by
        have h1 : ((fun k : ℕ => (k:ℝ)^j / k.factorial) (k+1)) = ((k:ℝ)+1)^j / ((k+1).factorial) := by
          push_cast; ring
        rw [h1, Real.norm_of_nonneg hfk1.le, Real.norm_of_nonneg hfk.le, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        field_simp
      rw [hratio]
      calc ((k:ℝ)+1)^j / (((k:ℝ)+1) * (k:ℝ)^j)
          ≤ ((2:ℝ)^j * (k:ℝ)^j) / (((k:ℝ)+1) * (k:ℝ)^j) := by
            gcongr
            rw [← mul_pow]; gcongr; linarith
        _ = (2:ℝ)^j / ((k:ℝ)+1) := by rw [mul_div_mul_right _ _ (by positivity)]
    · apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

/-- Complex form: `(k:ℂ)ʲ/(k!)ᵐ → 0` for `m ≥ 1` (norm `≤ kʲ/k!`). -/
theorem tendsto_cpow_div_factorial_pow (j m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => (k:ℂ)^j / (k.factorial : ℂ)^m) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (g := fun k : ℕ => (k:ℝ)^j / k.factorial)
  · intro k; positivity
  · intro k
    rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    have hf1 : (1:ℝ) ≤ (k.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hfm : (k.factorial : ℝ) ≤ (k.factorial : ℝ)^m := by
      calc (k.factorial:ℝ) = (k.factorial:ℝ)^(1 : ℕ) := (pow_one _).symm
        _ ≤ (k.factorial:ℝ)^m := pow_le_pow_right₀ hf1 hm
    gcongr
  · exact tendsto_natPow_div_factorial j

/-- For any polynomial `P` and `m ≥ 1`, `P(−k)/(k!)ᵐ → 0`: a finite sum of `(k:ℂ)ʲ/(k!)ᵐ` terms. -/
theorem poly_div_factorial_pow_tendsto (P : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => P.eval (-(k:ℂ)) / (k.factorial : ℂ)^m) atTop (𝓝 0) := by
  have hsum : ∀ k : ℕ, P.eval (-(k:ℂ)) / (k.factorial : ℂ)^m
      = ∑ j ∈ Finset.range (P.natDegree + 1),
          (P.coeff j * (-1)^j) * ((k:ℂ)^j / (k.factorial : ℂ)^m) := by
    intro k
    rw [Polynomial.eval_eq_sum_range, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [neg_pow]; ring
  simp_rw [hsum]
  rw [show (0:ℂ) = ∑ j ∈ Finset.range (P.natDegree + 1), (0:ℂ) by simp]
  apply tendsto_finsetSum
  intro j _
  simpa using (tendsto_cpow_div_factorial_pow j m hm).const_mul (P.coeff j * (-1)^j)

/-- **The building block of factorial domination:** `P(−k)·((−1)^k/k!)ᵐ → 0` for `m ≥ 1`
(the sign is a unit, so this has the same norm as `P(−k)/(k!)ᵐ`). -/
theorem poly_mul_rk_pow_tendsto (P : Polynomial ℂ) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun k : ℕ => P.eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^m) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have heq : ∀ k : ℕ, ‖P.eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^m‖
      = ‖P.eval (-(k:ℂ)) / (k.factorial : ℂ)^m‖ := by
    intro k
    rw [norm_mul, norm_div, norm_pow, norm_div, norm_pow]
    congr 1
    rw [norm_pow]
    simp
  simp_rw [heq]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  exact poly_div_factorial_pow_tendsto P m hm

/-- **Factorial-Dirichlet domination (the arithmetic core of nonlinear Hölder).**  If a finite
"factorial-Dirichlet polynomial" `∑_{D∈S} P_D(−k)·((−1)^k/k!)^D` vanishes for every `k`, then every
coefficient polynomial `P_D ≡ 0`.  Proof: dividing by `((−1)^k/k!)^{D₀}` for `D₀ = min S`, the `D₀`
term is `P_{D₀}(−k)` and every other term carries `((−1)^k/k!)^{D−D₀} → 0` (`poly_mul_rk_pow_tendsto`),
so `P_{D₀}(−k) → 0`, hence `P_{D₀} ≡ 0` (`poly_eval_neg_tendsto_zero_imp_zero`); then strong induction on
the remaining `S.erase D₀`.  This is exactly the `(k!)`-domination that finishes the first-order
non-linear Hölder theorem, where — the jet `(Γ,Γ')` having no monomial ties — the leading Laurent
coefficient at each pole is such a factorial-Dirichlet polynomial. -/
theorem factorial_dirichlet_vanishing (S : Finset ℕ) (P : ℕ → Polynomial ℂ)
    (h : ∀ k : ℕ, ∑ D ∈ S, (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D = 0) :
    ∀ D ∈ S, P D = 0 := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · simp
    · set D₀ := S.min' hSne with hD₀
      have hD₀mem : D₀ ∈ S := S.min'_mem hSne
      have hrk : ∀ k : ℕ, ((-1:ℂ)^k / (k.factorial : ℂ)) ≠ 0 := fun k =>
        div_ne_zero (pow_ne_zero k (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)
      have hPD₀ : P D₀ = 0 := by
        apply poly_eval_neg_tendsto_zero_imp_zero
        have hid : ∀ k : ℕ, (P D₀).eval (-(k:ℂ))
            = - ∑ D ∈ S.erase D₀, (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(D - D₀) := by
          intro k
          have hdiv : ∑ D ∈ S, (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(D - D₀) = 0 := by
            have hfac : ∑ D ∈ S, (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D
                = ((-1)^k / (k.factorial : ℂ))^D₀ *
                  ∑ D ∈ S, (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(D - D₀) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun D hD => ?_)
              have hexp : ((-1:ℂ)^k / (k.factorial : ℂ))^D
                  = ((-1)^k / (k.factorial : ℂ))^D₀ * ((-1)^k / (k.factorial : ℂ))^(D - D₀) := by
                rw [← pow_add]; congr 1; have := S.min'_le D hD; omega
              rw [hexp]; ring
            rw [h k] at hfac
            exact (mul_eq_zero.mp hfac.symm).resolve_left (pow_ne_zero _ (hrk k))
          have hae := Finset.add_sum_erase S
            (fun D => (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(D - D₀)) hD₀mem
          rw [hdiv] at hae
          simp only [Nat.sub_self, pow_zero, mul_one] at hae
          exact eq_neg_of_add_eq_zero_left hae
        rw [show (fun k : ℕ => (P D₀).eval (-(k:ℂ))) = fun k : ℕ => - ∑ D ∈ S.erase D₀,
            (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(D - D₀) from funext hid]
        rw [show (0:ℂ) = -0 by ring]
        apply Tendsto.neg
        rw [show (0:ℂ) = ∑ D ∈ S.erase D₀, (0:ℂ) by simp]
        apply tendsto_finsetSum
        intro D hD
        have hDgt : 1 ≤ D - D₀ := by
          rw [Finset.mem_erase] at hD; have := S.min'_le D hD.2; omega
        exact poly_mul_rk_pow_tendsto (P D) (D - D₀) hDgt
      have hrest : ∀ D ∈ S.erase D₀, P D = 0 := by
        apply ih (S.erase D₀) (Finset.erase_ssubset hD₀mem)
        intro k
        rw [Finset.sum_erase_eq_sub hD₀mem, h k, hPD₀]
        simp
      intro D hD
      rcases eq_or_ne D D₀ with rfl | hne
      · exact hPD₀
      · exact hrest D (Finset.mem_erase.mpr ⟨hne, hD⟩)

/-- **First-order nonlinear Hölder with a lower-order remainder.**  The remainder-form of
`gamma_no_weightedHomog_firstOrder`: if the weighted-homogeneous degree-`d` part plus any remainder `Q`
that vanishes after multiplication by `(s+k)^d` (i.e. `Q` collects only strictly-lower-weighted-degree
monomials) sums to zero off the poles, the top coefficients `c_b` still all vanish.  This is the direct
route to the *general* (non-homogeneous) first-order theorem: split `P(s,Γ,Γ')` into its top
weighted-homogeneous part and the rest, the latter being exactly such a `Q`. -/
theorem gamma_no_weightedHomog_firstOrder_rem (N d : ℕ) (hd : 2 * N ≤ d) (c : ℕ → Polynomial ℂ)
    (Q : ℂ → ℂ) (hQ : ∀ k : ℕ, Tendsto (fun s : ℂ => (s + (k:ℂ))^d * Q s) (𝓝[≠] (-(k:ℂ))) (𝓝 0))
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      (∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 2*b) * (deriv Complex.Gamma s) ^ b) + Q s = 0) :
    ∀ b ∈ range (N+1), c b = 0 := by
  set P : ℕ → Polynomial ℂ := fun D => (-1)^(d - D) * c (d - D) with hP
  have hdom : ∀ k : ℕ, ∑ D ∈ (range (N+1)).image (fun b => d - b),
      (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D = 0 := by
    intro k
    have hev0 : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^d *
        (∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 2*b) * (deriv Complex.Gamma s) ^ b)
        = -((s + (k:ℂ))^d * Q s) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
        with s hsb hsne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
      have hr := hrel s (ball_avoids hsb hsne)
      linear_combination (s + (k:ℂ))^d * hr
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^d *
        ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 2*b) * (deriv Complex.Gamma s) ^ b)
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hQneg : Tendsto (fun s : ℂ => -((s + (k:ℂ))^d * Q s)) (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
        have h := (hQ k).neg; rwa [neg_zero] at h
      exact hQneg.congr' (hev0.mono (fun _ h => h.symm))
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^d *
        ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 2*b) * (deriv Complex.Gamma s) ^ b)
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (∑ b ∈ range (N+1), (c b).eval (-(k:ℂ)) *
          (((-1)^k / (k.factorial : ℂ))^(d - 2*b) * (-((-1)^k / (k.factorial : ℂ)))^b))) := by
      simp only [Finset.mul_sum]
      apply tendsto_finsetSum
      intro b hb
      rw [mem_range, Nat.lt_succ_iff] at hb
      have hbd : 2 * b ≤ d := by omega
      have hcb : Tendsto (fun s : ℂ => (c b).eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 ((c b).eval (-(k:ℂ)))) :=
        (c b).continuous.continuousAt.continuousWithinAt
      have hmono := ((gamma_residue k).pow (d - 2*b)).mul ((gamma_deriv_residue k).pow b)
      have hfun : (fun s : ℂ => (s + (k:ℂ))^d *
          ((c b).eval s * Complex.Gamma s ^ (d - 2*b) * (deriv Complex.Gamma s) ^ b))
          = fun s : ℂ => (c b).eval s *
            (((s + (k:ℂ)) * Complex.Gamma s)^(d - 2*b) * ((s + (k:ℂ))^(2 : ℕ) * deriv Complex.Gamma s)^b) := by
        funext s
        have he1 : (d - 2*b) + 2*b = d := by omega
        rw [mul_pow, mul_pow, ← pow_mul,
          show (s + (k:ℂ))^(d-2*b) * Complex.Gamma s^(d-2*b) * ((s+(k:ℂ))^(2*b) * (deriv Complex.Gamma s)^b)
            = (s+(k:ℂ))^((d-2*b) + 2*b) * (Complex.Gamma s^(d-2*b) * (deriv Complex.Gamma s)^b) by
              rw [pow_add]; ring, he1]
        ring
      rw [hfun]
      exact hcb.mul hmono
    have hval := tendsto_nhds_unique hlim0 hlim1
    rw [Finset.sum_image (by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, mem_range, Nat.lt_succ_iff] at hx hy
      have hxy' : d - x = d - y := hxy
      omega)]
    refine Eq.trans (Finset.sum_congr rfl fun b hb => ?_) hval.symm
    rw [mem_range, Nat.lt_succ_iff] at hb
    show (P (d - b)).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(d - b)
      = (c b).eval (-(k:ℂ)) *
        (((-1)^k / (k.factorial : ℂ))^(d - 2*b) * (-((-1)^k / (k.factorial : ℂ)))^b)
    have he2 : (d - 2*b) + b = d - b := by omega
    have he3 : d - (d - b) = b := by omega
    simp only [hP, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
      Polynomial.eval_one, he3]
    rw [neg_pow]
    have hpow : ((-1:ℂ)^k / (k.factorial:ℂ))^(d-2*b) * ((-1:ℂ)^k / (k.factorial:ℂ))^b
        = ((-1:ℂ)^k / (k.factorial:ℂ))^(d-b) := by rw [← pow_add, he2]
    linear_combination (-((c b).eval (-(k:ℂ)) * (-1:ℂ)^b)) * hpow
  have hPzero := factorial_dirichlet_vanishing _ P hdom
  intro b hb
  rw [mem_range, Nat.lt_succ_iff] at hb
  have hDmem : d - b ∈ (range (N+1)).image (fun b => d - b) :=
    Finset.mem_image.mpr ⟨b, mem_range.mpr (by omega), rfl⟩
  have hb0 := hPzero (d - b) hDmem
  simp only [hP, show d - (d - b) = b from by omega] at hb0
  rcases mul_eq_zero.mp hb0 with h | h
  · exact absurd h (pow_ne_zero b (by norm_num : (-1 : Polynomial ℂ) ≠ 0))
  · exact h

/-- **First-order nonlinear Hölder (weighted-homogeneous case).**  Γ satisfies no nontrivial
weighted-homogeneous first-order algebraic differential relation: if `∑_{b≤N} c_b(s)·Γ(s)^{d−2b}·(Γ'(s))^b`
vanishes off the poles (with `2N ≤ d`), then every coefficient `c_b ≡ 0`.  This is a genuinely
*nonlinear* differential-non-existence theorem for Γ — the analytic and arithmetic layers combined: each
monomial's residue `(s+k)^d·Γ^{d−2b}(Γ')^b → r_k^{d−2b}·(−r_k)^b` comes from `gamma_residue` and
`gamma_deriv_residue`; the two-variable jet `(Γ,Γ')` has no monomial ties, so the leading Laurent
coefficient at each pole is a factorial-Dirichlet polynomial, killed by `factorial_dirichlet_vanishing`. -/
theorem gamma_no_weightedHomog_firstOrder (N d : ℕ) (hd : 2 * N ≤ d) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 2*b) * (deriv Complex.Gamma s) ^ b = 0) :
    ∀ b ∈ range (N+1), c b = 0 :=
  gamma_no_weightedHomog_firstOrder_rem N d hd c (fun _ => 0)
    (fun k => by
      simpa only [mul_zero] using
        (tendsto_const_nhds (α := ℂ) (x := (0 : ℂ)) (f := 𝓝[≠] (-(k : ℂ)))))
    (fun s hs => by simpa using hrel s hs)

/-- **A non-homogeneous first-order nonlinear relation is impossible for Γ.**  Γ satisfies no
`c₀(s)·Γ² + c₁(s)·Γ' + c₂(s)·Γ + c₃(s) = 0` with `(c₀,c₁)` not both zero — a concrete general (mixed
weighted-degree 2,2,1,0) first-order case.  Proved by `gamma_no_weightedHomog_firstOrder_rem`: the
degree-2 part `c₀Γ² + c₁Γ'` is the weighted-homogeneous top, and `Q = c₂Γ + c₃` is the lower-order
remainder, which vanishes after `×(s+k)²` (`(s+k)²Γ → 0`, `(s+k)² → 0`).  Demonstrates the reduction of
the general first-order theorem to the remainder form via a finite check on the lower monomials. -/
theorem gamma_no_quadratic_firstOrder (c₀ c₁ c₂ c₃ : Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      c₀.eval s * Complex.Gamma s ^ 2 + c₁.eval s * deriv Complex.Gamma s
        + c₂.eval s * Complex.Gamma s + c₃.eval s = 0) :
    c₀ = 0 ∧ c₁ = 0 := by
  set cc : ℕ → Polynomial ℂ := fun b => if b = 0 then c₀ else c₁ with hcc
  have hQ : ∀ k : ℕ, Tendsto (fun s : ℂ => (s + (k:ℂ))^(2 : ℕ) * (c₂.eval s * Complex.Gamma s + c₃.eval s))
      (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
    intro k
    have hz : Tendsto (fun s : ℂ => s + (k:ℂ)) (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have : Tendsto (fun s : ℂ => s + (k:ℂ)) (𝓝 (-(k:ℂ))) (𝓝 ((-(k:ℂ)) + (k:ℂ))) :=
        (continuous_id.add continuous_const).continuousAt
      rw [neg_add_cancel] at this; exact this.mono_left nhdsWithin_le_nhds
    have hg2 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(2 : ℕ) * Complex.Gamma s) (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have := hz.mul (gamma_residue k); simp only [zero_mul] at this
      refine this.congr' ?_; filter_upwards with s; ring
    have hsq : Tendsto (fun s : ℂ => (s + (k:ℂ))^(2 : ℕ)) (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have := hz.mul hz; simp only [mul_zero] at this
      refine this.congr' ?_; filter_upwards with s; ring
    have hc2 : Tendsto (fun s : ℂ => c₂.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₂.eval (-(k:ℂ)))) :=
      c₂.continuous.continuousAt.continuousWithinAt
    have hc3 : Tendsto (fun s : ℂ => c₃.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₃.eval (-(k:ℂ)))) :=
      c₃.continuous.continuousAt.continuousWithinAt
    have hfeq : (fun s : ℂ => (s + (k:ℂ))^(2 : ℕ) * (c₂.eval s * Complex.Gamma s + c₃.eval s))
        = fun s : ℂ => c₂.eval s * ((s + (k:ℂ))^(2 : ℕ) * Complex.Gamma s) + c₃.eval s * (s + (k:ℂ))^(2 : ℕ) := by
      funext s; ring
    rw [hfeq]
    simpa using (hc2.mul hg2).add (hc3.mul hsq)
  have hmain := gamma_no_weightedHomog_firstOrder_rem 1 2 (by norm_num) cc
    (fun s => c₂.eval s * Complex.Gamma s + c₃.eval s) hQ (by
      intro s hs
      have hr := hrel s hs
      simp only [hcc, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        if_true, if_neg (by norm_num : (1:ℕ) ≠ 0)]
      simp only [Nat.mul_zero, Nat.sub_zero, Nat.sub_self, pow_zero, mul_one, pow_one]
      linear_combination hr)
  refine ⟨?_, ?_⟩
  · have := hmain 0 (mem_range.mpr (by norm_num))
    simpa [hcc] using this
  · have := hmain 1 (mem_range.mpr (by norm_num))
    simpa [hcc] using this

/-- **An order-2 nonlinear relation is impossible for Γ (the tie-free `Γ,Γ''` direction).**  Γ satisfies
no `c₀(s)·Γ³ + c₁(s)·Γ'' = 0` with `(c₀,c₁)` not both zero.  This reaches *second* order: the jet
`(Γ, Γ'')` has pole orders `1` and `3`, and the two monomials `Γ³` (total degree 3) and `Γ''`
(total degree 1) sit at *distinct* total degrees, so no monomial tie forms — the leading Laurent
coefficients at the poles `−k` separate by the `factorial_dirichlet_vanishing` domination over the two
`r_k`-powers `{r_k, r_k³}`.  Residues: `(s+k)Γ → r_k` (`gamma_residue`) and `(s+k)³Γ'' → 2r_k`
(`gamma_iteratedDeriv_residue 2`).  The obstruction to *general* order-2 Hölder — the `(Γ')²` vs `Γ·Γ''`
tie at equal weighted and total degree — is exactly what this `Γ'`-free relation avoids. -/
theorem gamma_no_cubic_GammaSecondDeriv (c₀ c₁ : Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      c₀.eval s * Complex.Gamma s ^ 3 + c₁.eval s * iteratedDeriv 2 Complex.Gamma s = 0) :
    c₀ = 0 ∧ c₁ = 0 := by
  set P : ℕ → Polynomial ℂ := fun D => if D = 3 then c₀ else 2 * c₁ with hP
  have hdom : ∀ k : ℕ, ∑ D ∈ ({1, 3} : Finset ℕ),
      (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D = 0 := by
    intro k
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(3 : ℕ) *
        (c₀.eval s * Complex.Gamma s ^ 3 + c₁.eval s * iteratedDeriv 2 Complex.Gamma s))
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hev : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^(3 : ℕ) *
          (c₀.eval s * Complex.Gamma s ^ 3 + c₁.eval s * iteratedDeriv 2 Complex.Gamma s) = 0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
          with s hsb hsne
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
        rw [hrel s (ball_avoids hsb hsne), mul_zero]
      exact tendsto_const_nhds.congr' (hev.mono (fun _ h => h.symm))
    have hc0 : Tendsto (fun s : ℂ => c₀.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₀.eval (-(k:ℂ)))) :=
      c₀.continuous.continuousAt.continuousWithinAt
    have hc1 : Tendsto (fun s : ℂ => c₁.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₁.eval (-(k:ℂ)))) :=
      c₁.continuous.continuousAt.continuousWithinAt
    have hg3 := (gamma_residue k).pow 3
    have hg2 := gamma_iteratedDeriv_residue 2 k
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(3 : ℕ) *
        (c₀.eval s * Complex.Gamma s ^ 3 + c₁.eval s * iteratedDeriv 2 Complex.Gamma s))
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (c₀.eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(3 : ℕ)
          + c₁.eval (-(k:ℂ)) * ((-1)^(2 : ℕ) * ((2:ℕ).factorial:ℂ) * ((-1)^k / (k.factorial : ℂ))))) := by
      have hfeq : (fun s : ℂ => (s + (k:ℂ))^(3 : ℕ) *
          (c₀.eval s * Complex.Gamma s ^ 3 + c₁.eval s * iteratedDeriv 2 Complex.Gamma s))
          = fun s : ℂ => c₀.eval s * ((s + (k:ℂ)) * Complex.Gamma s)^(3 : ℕ)
            + c₁.eval s * ((s + (k:ℂ))^(2+1) * iteratedDeriv 2 Complex.Gamma s) := by
        funext s; rw [mul_pow]; ring
      rw [hfeq]
      exact (hc0.mul hg3).add (hc1.mul hg2)
    have hval := tendsto_nhds_unique hlim0 hlim1
    have h2f : ((2:ℕ).factorial:ℂ) = 2 := by norm_num
    rw [h2f] at hval
    rw [Finset.sum_pair (by norm_num : (1:ℕ) ≠ 3), hP]
    simp only [if_neg (by norm_num : (1:ℕ) ≠ 3), if_true]
    have e2 : (2 * c₁ : Polynomial ℂ).eval (-(k:ℂ)) = 2 * c₁.eval (-(k:ℂ)) := by simp
    rw [e2]
    linear_combination -hval
  have hz := factorial_dirichlet_vanishing {1, 3} P hdom
  have h3 := hz 3 (by decide)
  have h1 := hz 1 (by decide)
  simp only [hP, if_pos rfl] at h3
  simp only [hP, if_neg (by norm_num : (1:ℕ) ≠ 3)] at h1
  refine ⟨h3, ?_⟩
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h (by norm_num)
  · exact h

/-- **A two-term nonlinear relation `Γ^{j+1}` vs `Γ^{(j)}` is impossible for Γ, at every order `j ≥ 1`.**
Γ satisfies no `c₀(s)·Γ^{j+1} + c₁(s)·Γ^{(j)} = 0` with `(c₀,c₁)` not both zero.  The jet `(Γ, Γ^{(j)})`
has pole orders `1` and `j+1`, and the two monomials `Γ^{j+1}` (total degree `j+1`) and `Γ^{(j)}` (total
degree `1`) sit at distinct total degrees, so no monomial tie forms — the leading Laurent coefficients
at `−k` separate by `factorial_dirichlet_vanishing` over `{r_k, r_k^{j+1}}`.  Residues `(s+k)Γ → r_k`
(`gamma_residue`) and `(s+k)^{j+1}·Γ^{(j)} → (−1)^j·j!·r_k` (`gamma_iteratedDeriv_residue j`).  Reaching
arbitrary order in the single-derivative direction; `j=1` and `j=2` recover the first-order and cubic
cases. -/
theorem gamma_no_twoTerm_GammaJthDeriv (j : ℕ) (hj : 1 ≤ j) (c₀ c₁ : Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      c₀.eval s * Complex.Gamma s ^ (j+1) + c₁.eval s * iteratedDeriv j Complex.Gamma s = 0) :
    c₀ = 0 ∧ c₁ = 0 := by
  set P : ℕ → Polynomial ℂ :=
    fun D => if D = j+1 then c₀ else Polynomial.C ((-1)^j * (j.factorial:ℂ)) * c₁ with hP
  have hne1 : (1:ℕ) ≠ j + 1 := by omega
  have hdom : ∀ k : ℕ, ∑ D ∈ ({1, j+1} : Finset ℕ),
      (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D = 0 := by
    intro k
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(j+1) *
        (c₀.eval s * Complex.Gamma s ^ (j+1) + c₁.eval s * iteratedDeriv j Complex.Gamma s))
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hev : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^(j+1) *
          (c₀.eval s * Complex.Gamma s ^ (j+1) + c₁.eval s * iteratedDeriv j Complex.Gamma s) = 0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
          with s hsb hsne
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
        rw [hrel s (ball_avoids hsb hsne), mul_zero]
      exact tendsto_const_nhds.congr' (hev.mono (fun _ h => h.symm))
    have hc0 : Tendsto (fun s : ℂ => c₀.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₀.eval (-(k:ℂ)))) :=
      c₀.continuous.continuousAt.continuousWithinAt
    have hc1 : Tendsto (fun s : ℂ => c₁.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₁.eval (-(k:ℂ)))) :=
      c₁.continuous.continuousAt.continuousWithinAt
    have hgpow := (gamma_residue k).pow (j+1)
    have hgj := gamma_iteratedDeriv_residue j k
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(j+1) *
        (c₀.eval s * Complex.Gamma s ^ (j+1) + c₁.eval s * iteratedDeriv j Complex.Gamma s))
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (c₀.eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(j+1)
          + c₁.eval (-(k:ℂ)) * ((-1)^j * (j.factorial:ℂ) * ((-1)^k / (k.factorial : ℂ))))) := by
      have hfeq : (fun s : ℂ => (s + (k:ℂ))^(j+1) *
          (c₀.eval s * Complex.Gamma s ^ (j+1) + c₁.eval s * iteratedDeriv j Complex.Gamma s))
          = fun s : ℂ => c₀.eval s * ((s + (k:ℂ)) * Complex.Gamma s)^(j+1)
            + c₁.eval s * ((s + (k:ℂ))^(j+1) * iteratedDeriv j Complex.Gamma s) := by
        funext s; rw [mul_pow]; ring
      rw [hfeq]
      exact (hc0.mul hgpow).add (hc1.mul hgj)
    have hval := tendsto_nhds_unique hlim0 hlim1
    rw [Finset.sum_pair hne1, hP]
    simp only [hne1, if_false, if_true, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination -hval
  have hz := factorial_dirichlet_vanishing {1, j+1} P hdom
  have hj1 := hz (j+1) (by simp)
  have h1 := hz 1 (by simp)
  simp only [hP, if_true] at hj1
  simp only [hP, hne1, if_false] at h1
  refine ⟨hj1, ?_⟩
  rcases mul_eq_zero.mp h1 with h | h
  · rw [Polynomial.C_eq_zero] at h
    exact absurd h (mul_ne_zero (pow_ne_zero j (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero j))
  · exact h

/-- **The full weighted-homogeneous order-2 Hölder theorem in the tie-free `Γ,Γ''` direction.**  Γ
satisfies no nontrivial weighted-homogeneous relation `∑_{c≤N} c_c(s)·Γ^{d−3c}·(Γ'')^c = 0` (with
`3N ≤ d`): every coefficient `c_c ≡ 0`.  This is the `(Γ, Γ'')` analogue of
`gamma_no_weightedHomog_firstOrder` at *arbitrary term count* — the second-derivative jet has pole
orders `1, 3`, so a monomial `Γ^{d−3c}·(Γ'')^c` sits at total degree `d−2c`, all distinct, giving no
tie.  The leading Laurent coefficient at `−k` is a factorial-Dirichlet polynomial over the powers
`r_k^{d−2c}`, killed by `factorial_dirichlet_vanishing`; residues `(s+k)Γ → r_k` and
`(s+k)³·Γ'' → 2·r_k` (`gamma_iteratedDeriv_residue 2`).  Reaches the full nonlinear order-2 theory
wherever the mixed `(Γ')²`/`Γ·Γ''` tie is absent. -/
theorem gamma_no_weightedHomog_GammaSecondDeriv (N d : ℕ) (hd : 3 * N ≤ d) (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 3*b)
        * (iteratedDeriv 2 Complex.Gamma s) ^ b = 0) :
    ∀ b ∈ range (N+1), c b = 0 := by
  set P : ℕ → Polynomial ℂ := fun D => (2:Polynomial ℂ)^((d - D)/2) * c ((d - D)/2) with hP
  have hdom : ∀ k : ℕ, ∑ D ∈ (range (N+1)).image (fun b => d - 2*b),
      (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D = 0 := by
    intro k
    have hg2 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(2+1) * iteratedDeriv 2 Complex.Gamma s)
        (𝓝[≠] (-(k:ℂ))) (𝓝 (2 * ((-1)^k / (k.factorial : ℂ)))) := by
      have h := gamma_iteratedDeriv_residue 2 k
      convert h using 2; norm_num
    have hev0 : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^d *
        ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 3*b)
          * (iteratedDeriv 2 Complex.Gamma s) ^ b = 0 := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
        with s hsb hsne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
      rw [hrel s (ball_avoids hsb hsne), mul_zero]
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^d *
        ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 3*b)
          * (iteratedDeriv 2 Complex.Gamma s) ^ b)
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := tendsto_const_nhds.congr' (hev0.mono (fun _ h => h.symm))
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^d *
        ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - 3*b)
          * (iteratedDeriv 2 Complex.Gamma s) ^ b)
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (∑ b ∈ range (N+1), (c b).eval (-(k:ℂ)) *
          (((-1)^k / (k.factorial : ℂ))^(d - 3*b) * (2 * ((-1)^k / (k.factorial : ℂ)))^b))) := by
      simp only [Finset.mul_sum]
      apply tendsto_finsetSum
      intro b hb
      rw [mem_range, Nat.lt_succ_iff] at hb
      have hbd : 3 * b ≤ d := by omega
      have hcb : Tendsto (fun s : ℂ => (c b).eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 ((c b).eval (-(k:ℂ)))) :=
        (c b).continuous.continuousAt.continuousWithinAt
      have hmono := ((gamma_residue k).pow (d - 3*b)).mul (hg2.pow b)
      have hfun : (fun s : ℂ => (s + (k:ℂ))^d *
          ((c b).eval s * Complex.Gamma s ^ (d - 3*b) * (iteratedDeriv 2 Complex.Gamma s) ^ b))
          = fun s : ℂ => (c b).eval s *
            (((s + (k:ℂ)) * Complex.Gamma s)^(d - 3*b)
              * ((s + (k:ℂ))^(2+1) * iteratedDeriv 2 Complex.Gamma s)^b) := by
        funext s
        have he1 : (d - 3*b) + 3*b = d := by omega
        rw [mul_pow, mul_pow, ← pow_mul,
          show (s + (k:ℂ))^(d-3*b) * Complex.Gamma s^(d-3*b)
              * ((s+(k:ℂ))^((2+1)*b) * (iteratedDeriv 2 Complex.Gamma s)^b)
            = (s+(k:ℂ))^((d-3*b) + 3*b)
              * (Complex.Gamma s^(d-3*b) * (iteratedDeriv 2 Complex.Gamma s)^b) by
              rw [pow_add]; ring_nf, he1]
        ring
      rw [hfun]
      exact hcb.mul hmono
    have hval := tendsto_nhds_unique hlim0 hlim1
    rw [Finset.sum_image (by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, mem_range, Nat.lt_succ_iff] at hx hy
      have hxy' : d - 2*x = d - 2*y := hxy
      omega)]
    refine Eq.trans (Finset.sum_congr rfl fun b hb => ?_) hval.symm
    rw [mem_range, Nat.lt_succ_iff] at hb
    show (P (d - 2*b)).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(d - 2*b)
      = (c b).eval (-(k:ℂ)) *
        (((-1)^k / (k.factorial : ℂ))^(d - 3*b) * (2 * ((-1)^k / (k.factorial : ℂ)))^b)
    have he2 : (d - 3*b) + b = d - 2*b := by omega
    have he3 : (d - (d - 2*b))/2 = b := by omega
    simp only [hP, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, he3]
    rw [mul_pow]
    have hpow : ((-1:ℂ)^k / (k.factorial:ℂ))^(d-3*b) * ((-1:ℂ)^k / (k.factorial:ℂ))^b
        = ((-1:ℂ)^k / (k.factorial:ℂ))^(d-2*b) := by rw [← pow_add, he2]
    linear_combination (-((c b).eval (-(k:ℂ)) * (2:ℂ)^b)) * hpow
  have hPzero := factorial_dirichlet_vanishing _ P hdom
  intro b hb
  rw [mem_range, Nat.lt_succ_iff] at hb
  have hDmem : d - 2*b ∈ (range (N+1)).image (fun b => d - 2*b) :=
    Finset.mem_image.mpr ⟨b, mem_range.mpr (by omega), rfl⟩
  have hb0 := hPzero (d - 2*b) hDmem
  simp only [hP, show (d - (d - 2*b))/2 = b from by omega] at hb0
  rcases mul_eq_zero.mp hb0 with h | h
  · exact absurd h (pow_ne_zero b (by norm_num : (2 : Polynomial ℂ) ≠ 0))
  · exact h

/-- **The weighted-homogeneous Hölder theorem for `Γ` and any single derivative, at every order.**
For each `j ≥ 1`, Γ satisfies no nontrivial weighted-homogeneous relation
`∑_{c≤N} c_c(s)·Γ^{d−(j+1)c}·(Γ^{(j)})^c = 0` (with `(j+1)N ≤ d`): every coefficient `c_c ≡ 0`.  The jet
`(Γ, Γ^{(j)})` has pole orders `1` and `j+1`, so a monomial `Γ^{d−(j+1)c}·(Γ^{(j)})^c` sits at total
degree `d − jc` — all distinct across `c`, hence *no monomial tie forms at any order `j`*.  The leading
Laurent coefficient at each pole `−k` is a factorial-Dirichlet polynomial over the powers `r_k^{d−jc}`,
killed by `factorial_dirichlet_vanishing`; residues `(s+k)Γ → r_k` (`gamma_residue`) and
`(s+k)^{j+1}·Γ^{(j)} → (−1)^j·j!·r_k` (`gamma_iteratedDeriv_residue j`).  This unifies and subsumes the
`j=1` (first-order) and `j=2` cases: the entire tie-free region of Hölder's theorem — every relation in
`Γ` and a single one of its derivatives — is proven.  Only genuinely mixed-derivative relations, where
`(Γ')²` and `Γ·Γ''` collide at equal weighted and total degree, fall outside. -/
theorem gamma_no_weightedHomog_GammaJthDeriv (j N d : ℕ) (hj : 1 ≤ j) (hd : (j+1) * N ≤ d)
    (c : ℕ → Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - (j+1)*b)
        * (iteratedDeriv j Complex.Gamma s) ^ b = 0) :
    ∀ b ∈ range (N+1), c b = 0 := by
  set P : ℕ → Polynomial ℂ :=
    fun D => (Polynomial.C ((-1)^j * (j.factorial:ℂ)))^((d - D)/j) * c ((d - D)/j) with hP
  have hdom : ∀ k : ℕ, ∑ D ∈ (range (N+1)).image (fun b => d - j*b),
      (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D = 0 := by
    intro k
    have hev0 : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^d *
        ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - (j+1)*b)
          * (iteratedDeriv j Complex.Gamma s) ^ b = 0 := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
        with s hsb hsne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
      rw [hrel s (ball_avoids hsb hsne), mul_zero]
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^d *
        ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - (j+1)*b)
          * (iteratedDeriv j Complex.Gamma s) ^ b)
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := tendsto_const_nhds.congr' (hev0.mono (fun _ h => h.symm))
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^d *
        ∑ b ∈ range (N+1), (c b).eval s * Complex.Gamma s ^ (d - (j+1)*b)
          * (iteratedDeriv j Complex.Gamma s) ^ b)
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (∑ b ∈ range (N+1), (c b).eval (-(k:ℂ)) *
          (((-1)^k / (k.factorial : ℂ))^(d - (j+1)*b)
            * ((-1)^j * (j.factorial:ℂ) * ((-1)^k / (k.factorial : ℂ)))^b))) := by
      simp only [Finset.mul_sum]
      apply tendsto_finsetSum
      intro b hb
      rw [mem_range, Nat.lt_succ_iff] at hb
      have hsm : (j+1)*b = j*b + b := by ring
      have hbd : (j+1)*b ≤ d := le_trans (by gcongr) hd
      have hjb : j*b + b ≤ d := hsm ▸ hbd
      have hcb : Tendsto (fun s : ℂ => (c b).eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 ((c b).eval (-(k:ℂ)))) :=
        (c b).continuous.continuousAt.continuousWithinAt
      have hmono := ((gamma_residue k).pow (d - (j+1)*b)).mul ((gamma_iteratedDeriv_residue j k).pow b)
      have hfun : (fun s : ℂ => (s + (k:ℂ))^d *
          ((c b).eval s * Complex.Gamma s ^ (d - (j+1)*b) * (iteratedDeriv j Complex.Gamma s) ^ b))
          = fun s : ℂ => (c b).eval s *
            (((s + (k:ℂ)) * Complex.Gamma s)^(d - (j+1)*b)
              * ((s + (k:ℂ))^(j+1) * iteratedDeriv j Complex.Gamma s)^b) := by
        funext s
        have he1 : (d - (j+1)*b) + (j+1)*b = d := Nat.sub_add_cancel hbd
        rw [mul_pow, mul_pow, ← pow_mul,
          show (s + (k:ℂ))^(d-(j+1)*b) * Complex.Gamma s^(d-(j+1)*b)
              * ((s+(k:ℂ))^((j+1)*b) * (iteratedDeriv j Complex.Gamma s)^b)
            = (s+(k:ℂ))^((d-(j+1)*b) + (j+1)*b)
              * (Complex.Gamma s^(d-(j+1)*b) * (iteratedDeriv j Complex.Gamma s)^b) by
              rw [pow_add]; ring, he1]
        ring
      rw [hfun]
      exact hcb.mul hmono
    have hval := tendsto_nhds_unique hlim0 hlim1
    rw [Finset.sum_image (by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, mem_range, Nat.lt_succ_iff] at hx hy
      have hjxd : j * x ≤ d := le_trans (le_trans (by gcongr; omega) (by gcongr : (j+1)*x ≤ (j+1)*N)) hd
      have hjyd : j * y ≤ d := le_trans (le_trans (by gcongr; omega) (by gcongr : (j+1)*y ≤ (j+1)*N)) hd
      have hxy' : d - j*x = d - j*y := hxy
      have : j * x = j * y := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) this)]
    refine Eq.trans (Finset.sum_congr rfl fun b hb => ?_) hval.symm
    rw [mem_range, Nat.lt_succ_iff] at hb
    have hsm : (j+1)*b = j*b + b := by ring
    have hbd : (j+1)*b ≤ d := le_trans (by gcongr) hd
    have hjb : j*b + b ≤ d := hsm ▸ hbd
    show (P (d - j*b)).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^(d - j*b)
      = (c b).eval (-(k:ℂ)) *
        (((-1)^k / (k.factorial : ℂ))^(d - (j+1)*b)
          * ((-1)^j * (j.factorial:ℂ) * ((-1)^k / (k.factorial : ℂ)))^b)
    have he2 : (d - (j+1)*b) + b = d - j*b := by rw [hsm]; omega
    have he3 : (d - (d - j*b))/j = b := by
      have hdd : d - (d - j*b) = j*b := by omega
      rw [hdd, Nat.mul_div_cancel_left b (by omega : 0 < j)]
    simp only [hP, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, he3]
    rw [mul_pow]
    have hpow : ((-1:ℂ)^k / (k.factorial:ℂ))^(d-(j+1)*b) * ((-1:ℂ)^k / (k.factorial:ℂ))^b
        = ((-1:ℂ)^k / (k.factorial:ℂ))^(d-j*b) := by rw [← pow_add, he2]
    linear_combination (-((c b).eval (-(k:ℂ)) * ((-1:ℂ)^j * (j.factorial:ℂ))^b)) * hpow
  have hPzero := factorial_dirichlet_vanishing _ P hdom
  intro b hb
  rw [mem_range, Nat.lt_succ_iff] at hb
  have hbd : (j+1)*b ≤ d := le_trans (by gcongr) hd
  have hjb : j*b + b ≤ d := by rw [show (j+1)*b = j*b+b from by ring] at hbd; exact hbd
  have hDmem : d - j*b ∈ (range (N+1)).image (fun b => d - j*b) :=
    Finset.mem_image.mpr ⟨b, mem_range.mpr (by omega), rfl⟩
  have hb0 := hPzero (d - j*b) hDmem
  have he3 : (d - (d - j*b))/j = b := by
    have hdd : d - (d - j*b) = j*b := by omega
    rw [hdd, Nat.mul_div_cancel_left b (by omega : 0 < j)]
  simp only [hP, he3] at hb0
  rcases mul_eq_zero.mp hb0 with h | h
  · exact absurd h (pow_ne_zero _ (Polynomial.C_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero j (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero j))))
  · exact h

/-- **A relation between two derivatives of Γ (excluding Γ itself) is impossible.**  Γ satisfies no
`c₀(s)·(Γ')³ + c₁(s)·(Γ'')² = 0` with `(c₀,c₁)` not both zero.  Both monomials have weighted degree `6`
(`(Γ')³`: pole order `2`, cubed; `(Γ'')²`: pole order `3`, squared), but total degrees `3` and `2` —
distinct, so no tie.  This shows the residue method reaches relations *between distinct derivatives*, not
only those involving `Γ`: any pair `(Γ^{(i)}, Γ^{(j)})` with `i ≠ j` is tie-free because the `2×2`
degree determinant `i−j ≠ 0` fixes the exponents.  The genuine `(Γ')²`/`Γ·Γ''` tie needs *three* jet
variables `(Γ, Γ', Γ'')`; no two-variable relation ever ties.  Residues `(s+k)²Γ' → −r_k`
(`gamma_deriv_residue`) and `(s+k)³Γ'' → 2r_k`; factorial-Dirichlet domination over `{r_k², r_k³}`. -/
theorem gamma_no_derivCubicSquare (c₀ c₁ : Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      c₀.eval s * (deriv Complex.Gamma s) ^ 3
        + c₁.eval s * (iteratedDeriv 2 Complex.Gamma s) ^ 2 = 0) :
    c₀ = 0 ∧ c₁ = 0 := by
  set P : ℕ → Polynomial ℂ :=
    fun D => if D = 3 then Polynomial.C ((-1:ℂ)) * c₀ else Polynomial.C (4:ℂ) * c₁ with hP
  have hdom : ∀ k : ℕ, ∑ D ∈ ({2, 3} : Finset ℕ),
      (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D = 0 := by
    intro k
    have hgd : Tendsto (fun s : ℂ => ((s + (k:ℂ))^(2 : ℕ) * deriv Complex.Gamma s)^(3 : ℕ))
        (𝓝[≠] (-(k:ℂ))) (𝓝 ((-((-1)^k / (k.factorial : ℂ)))^(3 : ℕ))) := (gamma_deriv_residue k).pow 3
    have hg2 : Tendsto (fun s : ℂ => ((s + (k:ℂ))^(2+1) * iteratedDeriv 2 Complex.Gamma s)^(2 : ℕ))
        (𝓝[≠] (-(k:ℂ))) (𝓝 (((-1)^(2 : ℕ) * (2 * 1 : ℂ) * ((-1)^k / (k.factorial : ℂ)))^(2 : ℕ))) := by
      have h := (gamma_iteratedDeriv_residue 2 k).pow 2; convert h using 3; norm_num
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(6 : ℕ) *
        (c₀.eval s * (deriv Complex.Gamma s) ^ 3 + c₁.eval s * (iteratedDeriv 2 Complex.Gamma s) ^ 2))
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hev : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^(6 : ℕ) *
          (c₀.eval s * (deriv Complex.Gamma s) ^ 3
            + c₁.eval s * (iteratedDeriv 2 Complex.Gamma s) ^ 2) = 0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
          with s hsb hsne
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
        rw [hrel s (ball_avoids hsb hsne), mul_zero]
      exact tendsto_const_nhds.congr' (hev.mono (fun _ h => h.symm))
    have hc0 : Tendsto (fun s : ℂ => c₀.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₀.eval (-(k:ℂ)))) :=
      c₀.continuous.continuousAt.continuousWithinAt
    have hc1 : Tendsto (fun s : ℂ => c₁.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₁.eval (-(k:ℂ)))) :=
      c₁.continuous.continuousAt.continuousWithinAt
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(6 : ℕ) *
        (c₀.eval s * (deriv Complex.Gamma s) ^ 3 + c₁.eval s * (iteratedDeriv 2 Complex.Gamma s) ^ 2))
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (c₀.eval (-(k:ℂ)) * (-((-1)^k / (k.factorial : ℂ)))^(3 : ℕ)
          + c₁.eval (-(k:ℂ)) * ((-1)^(2 : ℕ) * (2 * 1 : ℂ) * ((-1)^k / (k.factorial : ℂ)))^(2 : ℕ))) := by
      have hfeq : (fun s : ℂ => (s + (k:ℂ))^(6 : ℕ) *
          (c₀.eval s * (deriv Complex.Gamma s) ^ 3 + c₁.eval s * (iteratedDeriv 2 Complex.Gamma s) ^ 2))
          = fun s : ℂ => c₀.eval s * ((s + (k:ℂ))^(2 : ℕ) * deriv Complex.Gamma s)^(3 : ℕ)
            + c₁.eval s * ((s + (k:ℂ))^(2+1) * iteratedDeriv 2 Complex.Gamma s)^(2 : ℕ) := by
        funext s
        rw [mul_pow, mul_pow, show ((s+(k:ℂ))^(2 : ℕ))^(3 : ℕ) = (s+(k:ℂ))^(6 : ℕ) by ring,
          show ((s+(k:ℂ))^(2+1))^(2 : ℕ) = (s+(k:ℂ))^(6 : ℕ) by ring]
        ring
      rw [hfeq]
      exact (hc0.mul hgd).add (hc1.mul hg2)
    have hval := tendsto_nhds_unique hlim0 hlim1
    have h2f : ((-1:ℂ)^(2 : ℕ) * (2 * 1 : ℂ))^(2 : ℕ) = 4 := by norm_num
    rw [Finset.sum_pair (by norm_num : (2:ℕ) ≠ 3), hP]
    simp only [if_neg (by norm_num : (2:ℕ) ≠ 3), if_true, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination -hval
  have hz := factorial_dirichlet_vanishing {2, 3} P hdom
  have h3 := hz 3 (by decide)
  have h2 := hz 2 (by decide)
  simp only [hP, if_true] at h3
  simp only [hP, if_neg (by norm_num : (2:ℕ) ≠ 3)] at h2
  constructor
  · rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (Polynomial.C_eq_zero.mp h) (by norm_num)
    · exact h
  · rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (Polynomial.C_eq_zero.mp h) (by norm_num)
    · exact h

/-- **A two-term relation between any two distinct derivatives of Γ is impossible.**  For any `i < j`,
Γ satisfies no `c₀(s)·(Γ^{(i)})^{j+1} + c₁(s)·(Γ^{(j)})^{i+1} = 0` with `(c₀,c₁)` not both zero.  Both
monomials have weighted degree `(i+1)(j+1)` (pole orders `i+1` and `j+1`), but total degrees `j+1` and
`i+1` — distinct since `i ≠ j`, so no tie.  This is the general two-variable two-term Hölder theorem: it
subsumes both the `Γ`-and-single-derivative case (`i = 0`, giving `Γ^{j+1}` vs `Γ^{(j)}`) and relations
purely between derivatives (e.g. `i=1, j=2`: `(Γ')³` vs `(Γ'')²`).  Residues
`(s+k)^{i+1}·Γ^{(i)} → (−1)^i·i!·r_k` and `(s+k)^{j+1}·Γ^{(j)} → (−1)^j·j!·r_k`
(`gamma_iteratedDeriv_residue`); factorial-Dirichlet domination over `{r_k^{i+1}, r_k^{j+1}}`. -/
theorem gamma_no_twoTerm_GammaDerivs (i j : ℕ) (hij : i < j) (c₀ c₁ : Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      c₀.eval s * (iteratedDeriv i Complex.Gamma s) ^ (j+1)
        + c₁.eval s * (iteratedDeriv j Complex.Gamma s) ^ (i+1) = 0) :
    c₀ = 0 ∧ c₁ = 0 := by
  set P : ℕ → Polynomial ℂ :=
    fun D => if D = j+1 then Polynomial.C (((-1:ℂ)^i * (i.factorial:ℂ))^(j+1)) * c₀
      else Polynomial.C (((-1:ℂ)^j * (j.factorial:ℂ))^(i+1)) * c₁ with hP
  have hne : i + 1 ≠ j + 1 := by omega
  have hE : (i+1) * (j+1) = (j+1) * (i+1) := by ring
  have hdom : ∀ k : ℕ, ∑ D ∈ ({i+1, j+1} : Finset ℕ),
      (P D).eval (-(k:ℂ)) * ((-1)^k / (k.factorial : ℂ))^D = 0 := by
    intro k
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^((i+1)*(j+1)) *
        (c₀.eval s * (iteratedDeriv i Complex.Gamma s) ^ (j+1)
          + c₁.eval s * (iteratedDeriv j Complex.Gamma s) ^ (i+1)))
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hev : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^((i+1)*(j+1)) *
          (c₀.eval s * (iteratedDeriv i Complex.Gamma s) ^ (j+1)
            + c₁.eval s * (iteratedDeriv j Complex.Gamma s) ^ (i+1)) = 0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
          with s hsb hsne
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
        rw [hrel s (ball_avoids hsb hsne), mul_zero]
      exact tendsto_const_nhds.congr' (hev.mono (fun _ h => h.symm))
    have hc0 : Tendsto (fun s : ℂ => c₀.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₀.eval (-(k:ℂ)))) :=
      c₀.continuous.continuousAt.continuousWithinAt
    have hc1 : Tendsto (fun s : ℂ => c₁.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (c₁.eval (-(k:ℂ)))) :=
      c₁.continuous.continuousAt.continuousWithinAt
    have hgi := (gamma_iteratedDeriv_residue i k).pow (j+1)
    have hgj := (gamma_iteratedDeriv_residue j k).pow (i+1)
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^((i+1)*(j+1)) *
        (c₀.eval s * (iteratedDeriv i Complex.Gamma s) ^ (j+1)
          + c₁.eval s * (iteratedDeriv j Complex.Gamma s) ^ (i+1)))
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (c₀.eval (-(k:ℂ)) * ((-1)^i * (i.factorial:ℂ) * ((-1)^k / (k.factorial : ℂ)))^(j+1)
          + c₁.eval (-(k:ℂ)) * ((-1)^j * (j.factorial:ℂ) * ((-1)^k / (k.factorial : ℂ)))^(i+1))) := by
      have hfeq : (fun s : ℂ => (s + (k:ℂ))^((i+1)*(j+1)) *
          (c₀.eval s * (iteratedDeriv i Complex.Gamma s) ^ (j+1)
            + c₁.eval s * (iteratedDeriv j Complex.Gamma s) ^ (i+1)))
          = fun s : ℂ => c₀.eval s * ((s + (k:ℂ))^(i+1) * iteratedDeriv i Complex.Gamma s)^(j+1)
            + c₁.eval s * ((s + (k:ℂ))^(j+1) * iteratedDeriv j Complex.Gamma s)^(i+1) := by
        funext s
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, hE]
        ring
      rw [hfeq]
      exact (hc0.mul hgi).add (hc1.mul hgj)
    have hval := tendsto_nhds_unique hlim0 hlim1
    rw [Finset.sum_pair hne, hP]
    simp only [hne, if_false, if_true, Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_pow, mul_pow]
    linear_combination -hval
  have hz := factorial_dirichlet_vanishing {i+1, j+1} P hdom
  have hjj := hz (j+1) (by simp)
  have hii := hz (i+1) (by simp)
  simp only [hP, if_true] at hjj
  simp only [hP, hne, if_false] at hii
  refine ⟨?_, ?_⟩
  · rcases mul_eq_zero.mp hjj with h | h
    · exact absurd (Polynomial.C_eq_zero.mp h)
        (pow_ne_zero _ (mul_ne_zero (pow_ne_zero i (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero i)))
    · exact h
  · rcases mul_eq_zero.mp hii with h | h
    · exact absurd (Polynomial.C_eq_zero.mp h)
        (pow_ne_zero _ (mul_ne_zero (pow_ne_zero j (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero j)))
    · exact h

/-- **The second-derivative log-derivative identity for Γ.**  At any point where `Γ` is twice
differentiable and nonzero, `Γ''·Γ − (Γ')² = Γ²·(Γ'/Γ)'` — the numerator of the quotient rule for the
log-derivative `ψ = Γ'/Γ`.  This is the algebraic core connecting Γ's second-order jet to the digamma:
the combination `Γ·Γ'' − (Γ')²`, which is exactly the leading obstruction in the mixed
`(Γ')²`/`Γ·Γ''` tie, equals `Γ²·ψ'`. -/
theorem gamma_secondDeriv_logDeriv_identity (s : ℂ) (hs : Complex.Gamma s ≠ 0)
    (h1 : DifferentiableAt ℂ Complex.Gamma s) (h2 : DifferentiableAt ℂ (deriv Complex.Gamma) s) :
    iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s - (deriv Complex.Gamma s)^(2 : ℕ)
      = (Complex.Gamma s)^(2 : ℕ) * deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s := by
  have hdd : deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
      = (deriv (deriv Complex.Gamma) s * Complex.Gamma s
        - deriv Complex.Gamma s * deriv Complex.Gamma s) / (Complex.Gamma s)^(2 : ℕ) :=
    deriv_div h2 h1 hs
  rw [hdd, show iteratedDeriv 2 Complex.Gamma s = deriv (deriv Complex.Gamma) s from by
    rw [iteratedDeriv_succ, iteratedDeriv_one]]
  field_simp

/-- **The mixed three-variable relation reduces to a first-order relation in the digamma jet.**  If
`α(s)·(Γ')² + β(s)·(Γ''·Γ) = 0` at a point where `Γ` is twice differentiable and nonzero, then
`(α+β)(s)·ψ² + β(s)·ψ' = 0` there, for the log-derivative `ψ = Γ'/Γ` (digamma).  Substituting the
identity `Γ·Γ'' = (Γ')² + Γ²·ψ'` and dividing by `Γ²` collapses the three jet variables `(Γ,Γ',Γ'')`
— where the `(Γ')²`/`Γ·Γ''` monomial tie obstructs the residue method — to two jet variables `(ψ,ψ')`.
This is the bridge that turns the sole remaining tie-obstructed case of Hölder's theorem for `Γ` into a
differential-non-existence question for the digamma. -/
theorem gamma_mixed_reduces_to_digamma (α β : Polynomial ℂ) (s : ℂ) (hs : Complex.Gamma s ≠ 0)
    (h1 : DifferentiableAt ℂ Complex.Gamma s) (h2 : DifferentiableAt ℂ (deriv Complex.Gamma) s)
    (hrel : α.eval s * (deriv Complex.Gamma s)^(2 : ℕ)
      + β.eval s * (iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s) = 0) :
    (α.eval s + β.eval s) * (deriv Complex.Gamma s / Complex.Gamma s)^(2 : ℕ)
      + β.eval s * deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s = 0 := by
  have hid := gamma_secondDeriv_logDeriv_identity s hs h1 h2
  have hΓ2 : (Complex.Gamma s)^(2 : ℕ) ≠ 0 := pow_ne_zero 2 hs
  field_simp
  have key : α.eval s * (deriv Complex.Gamma s)^(2 : ℕ)
      + β.eval s * (iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s) = 0 := hrel
  rw [show iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s
    = (deriv Complex.Gamma s)^(2 : ℕ) + (Complex.Gamma s)^(2 : ℕ) * deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
    from by linear_combination hid] at key
  linear_combination key

/-- **The leading constraint on the mixed three-variable relation.**  If
`α(s)·(Γ')² + β(s)·(Γ''·Γ) = 0` off the poles, then `α + 2β = 0` as polynomials.  The two monomials
`(Γ')²` and `Γ·Γ''` both have weighted degree `4` and total degree `2` — the genuine tie — so at each
pole `−k` their leading Laurent coefficients add on the *same* power `r_k²`: multiplying by `(s+k)⁴` and
letting `s → −k` gives `(α(−k) + 2β(−k))·r_k² = 0`, hence `α(−k) + 2β(−k) = 0` for every `k` (residues
`(s+k)²Γ' → −r_k`, `(s+k)Γ·(s+k)³Γ'' → 2r_k²`).  Since `α + 2β` vanishes at the infinitely many points
`−k`, it is the zero polynomial.  Combined with the identity `Γ·Γ'' − 2(Γ')² = Γ²·(ψ' − ψ²)`
(`gamma_secondDeriv_logDeriv_identity`), this reduces the mixed case to `β·Γ²·(ψ' − ψ²) = 0`: the whole
tie collapses to `β = 0` once `ψ' − ψ²` (digamma) is shown not identically zero — the sole surviving
crux of Hölder's theorem for `Γ` in three jet variables. -/
theorem gamma_mixed_leading (α β : Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      α.eval s * (deriv Complex.Gamma s)^(2 : ℕ)
        + β.eval s * (iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s) = 0) :
    α + 2 * β = 0 := by
  have hroot : ∀ k : ℕ, (α + 2 * β).eval (-(k:ℂ)) = 0 := by
    intro k
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(4 : ℕ) *
        (α.eval s * (deriv Complex.Gamma s)^(2 : ℕ)
          + β.eval s * (iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s)))
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hev : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^(4 : ℕ) *
          (α.eval s * (deriv Complex.Gamma s)^(2 : ℕ)
            + β.eval s * (iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s)) = 0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
          with s hsb hsne
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
        rw [hrel s (ball_avoids hsb hsne), mul_zero]
      exact tendsto_const_nhds.congr' (hev.mono (fun _ h => h.symm))
    have hcα : Tendsto (fun s : ℂ => α.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (α.eval (-(k:ℂ)))) :=
      α.continuous.continuousAt.continuousWithinAt
    have hcβ : Tendsto (fun s : ℂ => β.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (β.eval (-(k:ℂ)))) :=
      β.continuous.continuousAt.continuousWithinAt
    have hgd := (gamma_deriv_residue k).pow 2
    have hgm := (gamma_residue k).mul (gamma_iteratedDeriv_residue 2 k)
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(4 : ℕ) *
        (α.eval s * (deriv Complex.Gamma s)^(2 : ℕ)
          + β.eval s * (iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s)))
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (α.eval (-(k:ℂ)) * (-((-1)^k / (k.factorial : ℂ)))^(2 : ℕ)
          + β.eval (-(k:ℂ)) * (((-1)^k / (k.factorial : ℂ))
            * ((-1)^(2 : ℕ) * ((2:ℕ).factorial : ℂ) * ((-1)^k / (k.factorial : ℂ)))))) := by
      have hfeq : (fun s : ℂ => (s + (k:ℂ))^(4 : ℕ) *
          (α.eval s * (deriv Complex.Gamma s)^(2 : ℕ)
            + β.eval s * (iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s)))
          = fun s : ℂ => α.eval s * ((s + (k:ℂ))^(2 : ℕ) * deriv Complex.Gamma s)^(2 : ℕ)
            + β.eval s * ((s + (k:ℂ)) * Complex.Gamma s
              * ((s + (k:ℂ))^(2+1) * iteratedDeriv 2 Complex.Gamma s)) := by
        funext s
        rw [mul_pow, show ((s+(k:ℂ))^(2 : ℕ))^(2 : ℕ) = (s+(k:ℂ))^(4 : ℕ) by ring]
        ring
      rw [hfeq]
      exact (hcα.mul hgd).add (hcβ.mul hgm)
    have hval := tendsto_nhds_unique hlim0 hlim1
    have hr : ((-1)^k / (k.factorial : ℂ)) ≠ 0 :=
      div_ne_zero (pow_ne_zero k (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)
    have hr2 : ((-1:ℂ)^k / (k.factorial : ℂ))^(2 : ℕ) ≠ 0 := pow_ne_zero 2 hr
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    have h2f : ((2:ℕ).factorial : ℂ) = 2 := by norm_num
    rw [h2f] at hval
    have hfinal : (α.eval (-(k:ℂ)) + 2 * β.eval (-(k:ℂ)))
        * ((-1)^k / (k.factorial : ℂ))^(2 : ℕ) = 0 := by
      linear_combination -hval
    rcases mul_eq_zero.mp hfinal with h | h
    · exact h
    · exact absurd h hr2
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => -(k:ℂ)) (fun a b hab => by simpa using hab)
  intro k
  exact hroot k

/-- **The Gamma derivative recurrence.**  Differentiating the functional equation `Γ(s+1) = s·Γ(s)`
gives `Γ(s) + s·Γ'(s) = Γ'(s+1)` at any `s` off the poles.  Equivalently `s·Γ' + Γ = Γ'∘(·+1)`; dividing
by `Γ` this is the digamma recurrence `ψ(s+1) = ψ(s) + 1/s`.  This is the functional-equation datum that
breaks the mixed `(Γ')²`/`Γ·Γ''` tie without any transcendental constant: it forces `s·Γ' + Γ` to equal
the nonzero `Γ'(s+1)`, so `s·Γ' + Γ ≢ 0` — exactly the quantity whose vanishing the tied relation would
require. -/
theorem gamma_deriv_recurrence (s : ℂ) (hs : ∀ n : ℕ, s ≠ -(n:ℂ)) :
    Complex.Gamma s + s * deriv Complex.Gamma s = deriv Complex.Gamma (s + 1) := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hΓs : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s hs
  have hs1 : ∀ n : ℕ, s + 1 ≠ -(n:ℂ) := by
    intro n h
    exact hs (n+1) (by push_cast; linear_combination h)
  have hΓs1 : DifferentiableAt ℂ Complex.Gamma (s + 1) := Complex.differentiableAt_Gamma (s + 1) hs1
  have hev : (fun z => Complex.Gamma (z + 1)) =ᶠ[𝓝 s] (fun z => z * Complex.Gamma z) := by
    filter_upwards [isOpen_ne.mem_nhds hs0] with z hz
    exact Complex.Gamma_add_one z hz
  have hcomp : deriv (fun z => Complex.Gamma (z + 1)) s = deriv Complex.Gamma (s + 1) := by
    have hd : HasDerivAt (fun z : ℂ => z + 1) 1 s := (hasDerivAt_id s).add_const 1
    have hc := hΓs1.hasDerivAt.comp s hd
    have hfun :
        (fun z => Complex.Gamma (z + 1)) = Complex.Gamma ∘ fun z : ℂ => z + 1 := by
      funext z
      rfl
    rw [hfun]
    simpa only [mul_one] using hc.deriv
  have hmul : deriv (fun z => z * Complex.Gamma z) s
      = Complex.Gamma s + s * deriv Complex.Gamma s := by
    have hfun : (fun z => z * Complex.Gamma z) = id * Complex.Gamma := by
      funext z
      rfl
    rw [hfun]
    simpa only [one_mul, id_eq] using ((hasDerivAt_id s).mul hΓs.hasDerivAt).deriv
  rw [← hmul, ← hcomp, hev.deriv_eq]

/-- **Γ' is not identically zero — constant-free.**  At least one of `Γ'(1), Γ'(2)` is nonzero.  If both
vanished, the recurrence `Γ(1) + 1·Γ'(1) = Γ'(2)` (`gamma_deriv_recurrence` at `s=1`) would give
`Γ(1) = 0`, contradicting `Γ(1) = 1`.  No transcendental constant (`γ`, `π`) is used — the functional
equation alone forces non-constancy.  Combined with `gamma_deriv_recurrence` (`s·Γ' + Γ = Γ'(s+1)`), this
gives that `s·Γ' + Γ` — the quantity whose identical vanishing the mixed `(Γ')²`/`Γ·Γ''` tie would
require — is not identically zero, the datum that breaks the tie. -/
theorem gamma_deriv_not_all_zero :
    deriv Complex.Gamma 1 ≠ 0 ∨ deriv Complex.Gamma 2 ≠ 0 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  rw [not_not] at h1 h2
  have hoff : ∀ n : ℕ, (1:ℂ) ≠ -(n:ℂ) := by
    intro n heq
    have hz : ((n+1:ℕ):ℂ) = 0 := by push_cast; linear_combination heq
    have : (n+1) = 0 := by exact_mod_cast hz
    omega
  have hr := gamma_deriv_recurrence 1 hoff
  rw [Complex.Gamma_one, h1, show (1:ℂ) + 1 = 2 by norm_num, h2] at hr
  simp at hr

/-- **Γ is analytic off the poles.**  At any `x ∉ −ℕ`, `Complex.Gamma` is analytic, obtained as the
inverse of the entire reciprocal `1/Γ` (nonzero exactly off the poles).  Exposes the analyticity that
`contDiffAt_Gamma` proves inline, giving `AnalyticAt` of every derivative and hence differentiability of
`Γ`, `Γ'`, `Γ''`, … at each point off `−ℕ`. -/
theorem analyticAt_Gamma (x : ℂ) (hx : ∀ n : ℕ, x ≠ -(n:ℂ)) : AnalyticAt ℂ Complex.Gamma x :=
  HTGeometry.analyticAt_Gamma_off_poles hx

/-- **`Γ·Γ'' − 2(Γ')²` is not identically zero — constant-free.**  If it vanished at every point off the
poles, the differentiated functional equation (`iteratedDeriv_Gamma_add_one`) would force, from its
values at `1` and `2`, that `Γ'(1) = −1`; feeding that into the value at `3` gives `F(3) = −2 ≠ 0`, a
contradiction.  No transcendental constant (`γ`, `π`) enters — the functional equation alone pins the
Taylor data enough to rule out `F ≡ 0`.  This is the datum that breaks the mixed `(Γ')²`/`Γ·Γ''` tie:
after the leading constraint `α = −2β` (`gamma_mixed_leading`), the relation becomes `β·F = 0`, so
`β ≡ 0` follows from `F ≢ 0` by the isolated-zeros principle. -/
private theorem off_poles_pos {x : ℂ} (hx : ∃ r : ℝ, 0 < r ∧ x = (r:ℂ)) : ∀ n : ℕ, x ≠ -(n:ℂ) := by
  obtain ⟨r, hr, rfl⟩ := hx
  intro n h
  have := congrArg Complex.re h
  simp at this
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem gamma_F_not_identically_zero :
    ¬ ∀ z : ℂ, (∀ n : ℕ, z ≠ -(n:ℂ)) →
      Complex.Gamma z * iteratedDeriv 2 Complex.Gamma z - 2 * (iteratedDeriv 1 Complex.Gamma z)^(2 : ℕ) = 0 := by
  intro hF
  have o1 : ∀ n : ℕ, (1:ℂ) ≠ -(n:ℂ) := off_poles_pos ⟨1, by norm_num, by norm_num⟩
  have o2 : ∀ n : ℕ, (2:ℂ) ≠ -(n:ℂ) := off_poles_pos ⟨2, by norm_num, by norm_num⟩
  have o3 : ∀ n : ℕ, (3:ℂ) ≠ -(n:ℂ) := off_poles_pos ⟨3, by norm_num, by norm_num⟩
  -- Gamma values
  have hg1 : Complex.Gamma 1 = 1 := Complex.Gamma_one
  have hg2 : Complex.Gamma 2 = 1 := by
    have h := Complex.Gamma_nat_eq_factorial 1; simp only [Nat.factorial_one, Nat.cast_one] at h
    convert h using 2; norm_num
  have hg3 : Complex.Gamma 3 = 2 := by
    have h := Complex.Gamma_nat_eq_factorial 2; simp only [Nat.factorial_two, Nat.cast_ofNat] at h
    convert h using 2; norm_num
  -- recurrences (iteratedDeriv_Gamma_add_one) at x = 1 and x = 2
  have r1_1 := iteratedDeriv_Gamma_add_one 1 1 o1
  have r2_1 := iteratedDeriv_Gamma_add_one 2 1 o1
  have r1_2 := iteratedDeriv_Gamma_add_one 1 2 o2
  have r2_2 := iteratedDeriv_Gamma_add_one 2 2 o2
  -- F = 0 at 1, 2, 3
  have hF1 := hF 1 o1
  have hF2 := hF 2 o2
  have hF3 := hF 3 o3
  -- normalize: 1+1 = 2, 2+1 = 3, iteratedDeriv 0 = Gamma
  simp only [show (1:ℕ)-1 = 0 from rfl, show (2:ℕ)-1 = 1 from rfl, iteratedDeriv_zero,
    show (1:ℂ)+1 = 2 by norm_num, show (2:ℂ)+1 = 3 by norm_num,
    Nat.cast_one, Nat.cast_ofNat, hg1, hg2, hg3, one_mul, mul_one] at r1_1 r2_1 r1_2 r2_2 hF1 hF2 hF3
  -- hF1 : iteratedDeriv 2 Γ 1 - 2*(iteratedDeriv 1 Γ 1)^(2 : ℕ) = 0
  -- substitute recurrences into hF2, hF3 (in terms of a = id1Γ1, b = id2Γ1)
  rw [r2_1, r1_1] at hF2
  have ha : iteratedDeriv 1 Complex.Gamma 1 = -1 := by linear_combination (hF1 - hF2) / 2
  have hb : iteratedDeriv 2 Complex.Gamma 1 = 2 := by rw [ha] at hF1; linear_combination hF1
  rw [r2_2, r1_2, r2_1, r1_1, ha, hb] at hF3
  norm_num at hF3

/-- **The domain of Γ (off the poles `−ℕ`) is open.**  The pole set `⋃ₙ {−n}` is locally finite (each
ball of radius `1` meets only the poles `−n` with `n < ‖z‖+1`), hence closed; its complement is open. -/
theorem offPoles_isOpen : IsOpen {z : ℂ | ∀ n : ℕ, z ≠ -(n:ℂ)} := by
  have hLF : LocallyFinite (fun n : ℕ => ({(-(n:ℂ))} : Set ℂ)) := by
    intro z
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds z one_pos, ?_⟩
    apply Set.Finite.subset (Set.finite_Iio ⌈‖z‖ + 1⌉₊)
    intro n hn
    obtain ⟨w, hwn, hwb⟩ := hn
    rw [Set.mem_singleton_iff] at hwn; subst hwn
    rw [Metric.mem_ball, Complex.dist_eq] at hwb
    rw [Set.mem_Iio, Nat.lt_ceil]
    have h1 : ‖(-(n:ℂ))‖ ≤ ‖-(n:ℂ) - z‖ + ‖z‖ := by
      have := norm_add_le (-(n:ℂ) - z) z; simpa using this
    have h2 : ‖(-(n:ℂ))‖ = (n:ℝ) := by rw [norm_neg, Complex.norm_natCast]
    rw [h2] at h1; linarith
  have hclosed : IsClosed (⋃ n : ℕ, ({(-(n:ℂ))} : Set ℂ)) :=
    hLF.isClosed_iUnion (fun n => isClosed_singleton)
  have heq : {z : ℂ | ∀ n : ℕ, z ≠ -(n:ℂ)} = (⋃ n : ℕ, ({(-(n:ℂ))} : Set ℂ))ᶜ := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion,
      Set.mem_singleton_iff, not_exists]
  rw [heq]; exact hclosed.isOpen_compl

/-- **The three-variable mixed relation is impossible for Γ — Hölder's theorem in the tie case.**  Γ
satisfies no `α(s)·(Γ')² + β(s)·(Γ''·Γ) = 0` with `(α,β)` not both zero.  This is the one case the
two-variable theory could not reach: `(Γ')²` and `Γ·Γ''` tie at weighted degree `4`, total degree `2`.
Proof: the leading Laurent coefficients force `α + 2β = 0` (`gamma_mixed_leading`), collapsing the
relation to `β·F = 0` off the poles, where `F = Γ·Γ'' − 2(Γ')²`.  Since `F ≢ 0`
(`gamma_F_not_identically_zero`, constant-free via the functional equation) and `F` is continuous, `F`
is nonzero on a neighborhood of some point off the poles; on that (open, by `offPoles_isOpen`)
neighborhood `β` vanishes, so `β` has infinitely many roots and `β ≡ 0`, whence `α = −2β = 0`.  The tie
— the sole obstruction beyond relations in two jet variables — is discharged. -/
theorem gamma_no_mixed_relation (α β : Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      α.eval s * (deriv Complex.Gamma s)^(2 : ℕ)
        + β.eval s * (iteratedDeriv 2 Complex.Gamma s * Complex.Gamma s) = 0) :
    α = 0 ∧ β = 0 := by
  have hlead : α + 2 * β = 0 := gamma_mixed_leading α β hrel
  have hFnz := gamma_F_not_identically_zero
  rw [not_forall] at hFnz
  obtain ⟨z₀, hz₀⟩ := hFnz
  rw [Classical.not_imp] at hz₀
  obtain ⟨hz₀off, hz₀F⟩ := hz₀
  -- β·F = 0 off poles
  have hβF : ∀ z : ℂ, (∀ m : ℕ, z ≠ -(m:ℂ)) →
      β.eval z * (Complex.Gamma z * iteratedDeriv 2 Complex.Gamma z
        - 2 * (iteratedDeriv 1 Complex.Gamma z)^(2 : ℕ)) = 0 := by
    intro z hz
    have h := hrel z hz
    have hα : α.eval z = -2 * β.eval z := by
      have h0 : (α + 2 * β).eval z = 0 := by rw [hlead]; exact Polynomial.eval_zero
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat] at h0
      linear_combination h0
    rw [iteratedDeriv_one]
    linear_combination h - (deriv Complex.Gamma z)^(2 : ℕ) * hα
  -- F continuous at z₀
  have hFcont : ContinuousAt (fun z => Complex.Gamma z * iteratedDeriv 2 Complex.Gamma z
      - 2 * (iteratedDeriv 1 Complex.Gamma z)^(2 : ℕ)) z₀ := by
    have cΓ : ContinuousAt Complex.Gamma z₀ := (contDiffAt_Gamma z₀ hz₀off 1).continuousAt
    have c2 : ContinuousAt (iteratedDeriv 2 Complex.Gamma) z₀ :=
      continuousAt_iteratedDeriv_of_contDiffAt (contDiffAt_Gamma z₀ hz₀off 2)
    have c1 : ContinuousAt (iteratedDeriv 1 Complex.Gamma) z₀ :=
      continuousAt_iteratedDeriv_of_contDiffAt (contDiffAt_Gamma z₀ hz₀off 1)
    exact (cΓ.mul c2).sub (continuousAt_const.mul (c1.pow 2))
  have hFne : ∀ᶠ z in 𝓝 z₀, Complex.Gamma z * iteratedDeriv 2 Complex.Gamma z
      - 2 * (iteratedDeriv 1 Complex.Gamma z)^(2 : ℕ) ≠ 0 := hFcont.eventually_ne hz₀F
  have hoff : ∀ᶠ z in 𝓝 z₀, ∀ m : ℕ, z ≠ -(m:ℂ) := offPoles_isOpen.mem_nhds hz₀off
  have hβ0 : ∀ᶠ z in 𝓝 z₀, β.eval z = 0 := by
    filter_upwards [hFne, hoff] with z hFz hoz
    exact (mul_eq_zero.mp (hβF z hoz)).resolve_right hFz
  have hβ : β = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hmem : {z : ℂ | β.eval z = 0} ∈ 𝓝 z₀ := hβ0
    exact (infinite_of_mem_nhds z₀ hmem).mono (fun z hz => hz)
  exact ⟨by linear_combination hlead - 2 * hβ, hβ⟩

/-- **The leading constraint on the four-variable tie.**  If the weighted-homogeneous degree-6
relation `alpha*(Gamma'')^(2 : ℕ) + beta*(Gamma'*Gamma''') + gamma*(Gamma*Gamma^(4)) = 0` holds off the poles,
then `4*alpha + 6*beta + 24*gamma = 0`.  All three monomials sit at weighted degree 6 and total degree 2
-- a THREE-way tie -- so their leading Laurent coefficients add on the single power `r_k^(2 : ℕ)` with residues
4, 6, 24 (from `(2 r_k)^(2 : ℕ)`, `(-r_k)(-6 r_k)`, `r_k * 24 r_k` via `gamma_iteratedDeriv_residue` at orders
2; 1,3; 0,4).  Vanishing at every pole forces the polynomial identity.  Unlike the three-variable tie
(one equation, two coefficients), this leaves a TWO-dimensional kernel: closing the four-variable case
needs two further subleading constraints, one more than the three-variable case required. -/
theorem gamma_leading_order4 (α β γ : Polynomial ℂ)
    (hrel : ∀ s : ℂ, (∀ m : ℕ, s ≠ -(m:ℂ)) →
      α.eval s * (iteratedDeriv 2 Complex.Gamma s)^(2 : ℕ)
        + β.eval s * (iteratedDeriv 1 Complex.Gamma s * iteratedDeriv 3 Complex.Gamma s)
        + γ.eval s * (Complex.Gamma s * iteratedDeriv 4 Complex.Gamma s) = 0) :
    4 * α + 6 * β + 24 * γ = 0 := by
  have hroot : ∀ k : ℕ, (4 * α + 6 * β + 24 * γ).eval (-(k:ℂ)) = 0 := by
    intro k
    set r : ℂ := (-1)^k / (k.factorial : ℂ) with hr
    have hrne : r ≠ 0 := div_ne_zero (pow_ne_zero k (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)
    have hlim0 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(6 : ℕ) *
        (α.eval s * (iteratedDeriv 2 Complex.Gamma s)^(2 : ℕ)
          + β.eval s * (iteratedDeriv 1 Complex.Gamma s * iteratedDeriv 3 Complex.Gamma s)
          + γ.eval s * (Complex.Gamma s * iteratedDeriv 4 Complex.Gamma s)))
        (𝓝[≠] (-(k:ℂ))) (𝓝 0) := by
      have hev : ∀ᶠ s in 𝓝[≠] (-(k:ℂ)), (s + (k:ℂ))^(6 : ℕ) *
          (α.eval s * (iteratedDeriv 2 Complex.Gamma s)^(2 : ℕ)
            + β.eval s * (iteratedDeriv 1 Complex.Gamma s * iteratedDeriv 3 Complex.Gamma s)
            + γ.eval s * (Complex.Gamma s * iteratedDeriv 4 Complex.Gamma s)) = 0 := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Metric.ball_mem_nhds (-(k:ℂ)) (show (0:ℝ) < 1/2 by norm_num)), self_mem_nhdsWithin]
          with s hsb hsne
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsne
        rw [hrel s (ball_avoids hsb hsne), mul_zero]
      exact tendsto_const_nhds.congr' (hev.mono (fun _ h => h.symm))
    have cα : Tendsto (fun s : ℂ => α.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (α.eval (-(k:ℂ)))) :=
      α.continuous.continuousAt.continuousWithinAt
    have cβ : Tendsto (fun s : ℂ => β.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (β.eval (-(k:ℂ)))) :=
      β.continuous.continuousAt.continuousWithinAt
    have cγ : Tendsto (fun s : ℂ => γ.eval s) (𝓝[≠] (-(k:ℂ))) (𝓝 (γ.eval (-(k:ℂ)))) :=
      γ.continuous.continuousAt.continuousWithinAt
    have g0 := gamma_iteratedDeriv_residue 0 k
    have g1 := gamma_iteratedDeriv_residue 1 k
    have g2 := gamma_iteratedDeriv_residue 2 k
    have g3 := gamma_iteratedDeriv_residue 3 k
    have g4 := gamma_iteratedDeriv_residue 4 k
    have hlim1 : Tendsto (fun s : ℂ => (s + (k:ℂ))^(6 : ℕ) *
        (α.eval s * (iteratedDeriv 2 Complex.Gamma s)^(2 : ℕ)
          + β.eval s * (iteratedDeriv 1 Complex.Gamma s * iteratedDeriv 3 Complex.Gamma s)
          + γ.eval s * (Complex.Gamma s * iteratedDeriv 4 Complex.Gamma s)))
        (𝓝[≠] (-(k:ℂ)))
        (𝓝 (α.eval (-(k:ℂ)) * ((-1)^(2 : ℕ) * ((2:ℕ).factorial:ℂ) * r)^(2 : ℕ)
          + β.eval (-(k:ℂ)) * (((-1)^(1 : ℕ) * ((1:ℕ).factorial:ℂ) * r) * ((-1)^(3 : ℕ) * ((3:ℕ).factorial:ℂ) * r))
          + γ.eval (-(k:ℂ)) * (((-1)^(0 : ℕ) * ((0:ℕ).factorial:ℂ) * r) * ((-1)^(4 : ℕ) * ((4:ℕ).factorial:ℂ) * r)))) := by
      have hfeq : (fun s : ℂ => (s + (k:ℂ))^(6 : ℕ) *
          (α.eval s * (iteratedDeriv 2 Complex.Gamma s)^(2 : ℕ)
            + β.eval s * (iteratedDeriv 1 Complex.Gamma s * iteratedDeriv 3 Complex.Gamma s)
            + γ.eval s * (Complex.Gamma s * iteratedDeriv 4 Complex.Gamma s)))
          = fun s : ℂ => α.eval s * ((s + (k:ℂ))^(2+1) * iteratedDeriv 2 Complex.Gamma s)^(2 : ℕ)
            + β.eval s * (((s + (k:ℂ))^(1+1) * iteratedDeriv 1 Complex.Gamma s)
                * ((s + (k:ℂ))^(3+1) * iteratedDeriv 3 Complex.Gamma s))
            + γ.eval s * (((s + (k:ℂ))^(0+1) * iteratedDeriv 0 Complex.Gamma s)
                * ((s + (k:ℂ))^(4+1) * iteratedDeriv 4 Complex.Gamma s)) := by
        funext s
        rw [iteratedDeriv_zero]
        ring
      rw [hfeq]
      exact ((cα.mul (g2.pow 2)).add (cβ.mul (g1.mul g3))).add (cγ.mul (g0.mul g4))
    have hval := tendsto_nhds_unique hlim0 hlim1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    have hfac : (α.eval (-(k:ℂ)) * ((-1:ℂ)^(2 : ℕ) * ((2:ℕ).factorial:ℂ) * r)^(2 : ℕ)
        + β.eval (-(k:ℂ)) * (((-1)^(1 : ℕ) * ((1:ℕ).factorial:ℂ) * r) * ((-1)^(3 : ℕ) * ((3:ℕ).factorial:ℂ) * r))
        + γ.eval (-(k:ℂ)) * (((-1)^(0 : ℕ) * ((0:ℕ).factorial:ℂ) * r) * ((-1)^(4 : ℕ) * ((4:ℕ).factorial:ℂ) * r)))
        = (4 * α.eval (-(k:ℂ)) + 6 * β.eval (-(k:ℂ)) + 24 * γ.eval (-(k:ℂ))) * r^(2 : ℕ) := by
      simp only [Nat.factorial]; push_cast; ring
    rw [hfac] at hval
    have : (4 * α.eval (-(k:ℂ)) + 6 * β.eval (-(k:ℂ)) + 24 * γ.eval (-(k:ℂ))) * r^(2 : ℕ) = 0 := hval.symm
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h (pow_ne_zero 2 hrne)
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => -(k:ℂ)) (fun a b hab => by simpa using hab)
  intro k; exact hroot k

/-- **The digamma difference equation.**  For `s` off the poles, `psi(s+1) = psi(s) + 1/s` where
`psi = Gamma'/Gamma` is the digamma: `deriv Gamma (s+1) / Gamma (s+1) = deriv Gamma s / Gamma s + 1/s`.
Divide the Gamma derivative recurrence `Gamma(s) + s*Gamma'(s) = Gamma'(s+1)` by `Gamma(s+1) = s*Gamma(s)`.
This is the difference-Galois handle on Gamma's hypertranscendence: the log-derivative satisfies a
first-order inhomogeneous difference equation with rational right-hand side `1/s`, a constraint no
differentially algebraic function meets -- the shift-side counterpart to the differential obstruction. -/
theorem digamma_recurrence (s : ℂ) (hs : ∀ n : ℕ, s ≠ -(n:ℂ)) :
    deriv Complex.Gamma (s + 1) / Complex.Gamma (s + 1)
      = deriv Complex.Gamma s / Complex.Gamma s + 1 / s := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hΓs : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hrec := gamma_deriv_recurrence s hs
  have hfe : Complex.Gamma (s + 1) = s * Complex.Gamma s := Complex.Gamma_add_one s hs0
  rw [hfe, ← hrec]
  field_simp
  ring

/-- **Γ is transcendental as a function.**  No nonzero polynomial `P` vanishes on `Γ`: there is no
`P != 0` with `P(Γ(z)) = 0` for all `z`.  Indeed `Γ(n+2) = (n+1)!`, and the factorials `(n+1)!` are
infinitely many distinct values, so such a `P` would have infinitely many roots and be zero.  This is the
order-0 layer of Hölder's theorem for `Γ`, proved directly from the integer values rather than via
hypertranscendence -- the transcendence that `hypertranscendental_imp_transcendental` would upgrade. -/
theorem gamma_transcendental :
    ¬ ∃ P : Polynomial ℂ, P ≠ 0 ∧ ∀ z : ℂ, P.eval (Complex.Gamma z) = 0 := by
  rintro ⟨P, hP, hroot⟩
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + 1).factorial : ℂ))
  · intro a b hab
    have hab2 : ((a + 1).factorial : ℂ) = ((b + 1).factorial : ℂ) := hab
    have h : (a + 1).factorial = (b + 1).factorial := Nat.cast_inj.mp hab2
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd h (by have := Nat.factorial_lt (n := a+1) (m := b+1) (by omega); omega)
    · exact heq
    · exact absurd h.symm (by have := Nat.factorial_lt (n := b+1) (m := a+1) (by omega); omega)
  · intro n
    have hg : Complex.Gamma ((n:ℂ) + 1 + 1) = ((n + 1).factorial : ℂ) := by
      have := Complex.Gamma_nat_eq_factorial (n + 1)
      push_cast at this
      convert this using 2
    have hr := hroot ((n:ℂ) + 1 + 1)
    rw [hg] at hr
    exact hr

/-- **The telescoped digamma difference equation.**  For `s` off the poles and any `n`,
`psi(s+n) = psi(s) + sum_{k<n} 1/(s+k)` where `psi = Gamma'/Gamma`:
`deriv Gamma (s+n)/Gamma(s+n) = deriv Gamma s/Gamma s + sum_{k in range n} 1/(s+k)`.  Iterating
`digamma_recurrence` (`psi(s+1)=psi(s)+1/s`).  At `s=1` this is `psi(n+1) = psi(1) + H_n` (the harmonic
numbers), the concrete telescoping that exhibits digamma's difference structure: the log-derivative of
Gamma accumulates the divergent harmonic series along integer shifts, the shift-side signature of
hypertranscendence. -/
theorem digamma_telescope (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) (n : ℕ) :
    deriv Complex.Gamma (s + n) / Complex.Gamma (s + n)
      = deriv Complex.Gamma s / Complex.Gamma s + ∑ k ∈ Finset.range n, 1 / (s + (k:ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : ∀ p : ℕ, s + (n:ℂ) ≠ -(p:ℂ) := by
      intro p h
      exact hs (p + n) (by push_cast at h ⊢; linear_combination h)
    have hrec := digamma_recurrence (s + (n:ℂ)) hsn
    rw [show s + ((n+1 : ℕ):ℂ) = (s + (n:ℂ)) + 1 by push_cast; ring, hrec, ih,
      Finset.sum_range_succ]
    ring

/-- **Digamma is transcendental as a function.**  No nonzero polynomial `P` vanishes on `psi = Gamma'/Gamma`
off the poles.  By `digamma_telescope` at `s=1`, `psi(n+1) = psi(1) + H_n` with `H_n = sum_{k<n} 1/(1+k)`
the harmonic partial sums, which are strictly increasing reals -- so the values `psi(n+1)` are pairwise
distinct, giving `P` infinitely many roots, hence `P = 0`.  The transcendence of the log-derivative,
proved from the difference equation alone (no transcendental constant) -- the shift-side analogue of
`gamma_transcendental`. -/
private theorem off_poles_natpos (a : ℕ) (ha : 1 ≤ a) : ∀ p : ℕ, (a:ℂ) ≠ -(p:ℂ) := by
  intro p h
  have hz : ((a + p : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
  have : a + p = 0 := by exact_mod_cast hz
  omega

theorem digamma_transcendental :
    ¬ ∃ P : Polynomial ℂ, P ≠ 0 ∧
      ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p:ℂ)) → P.eval (deriv Complex.Gamma z / Complex.Gamma z) = 0 := by
  rintro ⟨P, hP, hroot⟩
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  set hR : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, 1 / (1 + (k:ℝ)) with hRdef
  have hmono : StrictMono hR := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hRdef]
    simp only [Finset.sum_range_succ]
    have : (0:ℝ) < 1 / (1 + (n:ℝ)) := by positivity
    linarith
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => deriv Complex.Gamma 1 / Complex.Gamma 1 + ((hR n : ℝ) : ℂ))
  · intro a b hab
    have h2 : ((hR a : ℝ) : ℂ) = ((hR b : ℝ) : ℂ) := add_left_cancel hab
    exact hmono.injective (Complex.ofReal_inj.mp h2)
  · intro n
    have hcast : ((hR n : ℝ) : ℂ) = ∑ k ∈ Finset.range n, 1 / (1 + (k:ℂ)) := by
      rw [hRdef]; push_cast; ring
    have h1off : ∀ p : ℕ, (1:ℂ) ≠ -(p:ℂ) := by simpa using off_poles_natpos 1 (le_refl 1)
    have htel := digamma_telescope 1 h1off n
    have hoff : ∀ p : ℕ, (1:ℂ) + (n:ℂ) ≠ -(p:ℂ) := by
      have := off_poles_natpos (n + 1) (by omega)
      intro p hp; exact this p (by push_cast at hp ⊢; linear_combination hp)
    have hr := hroot ((1:ℂ) + (n:ℂ)) hoff
    rw [hcast]
    rw [← htel]
    exact hr

/-- **The trigamma difference equation.**  For `s` off the poles, `psi'(s+1) = psi'(s) - 1/s^(2 : ℕ)` where
`psi = Gamma'/Gamma`: differentiating the digamma recurrence `psi(s+1) = psi(s) + 1/s`, valid because the
domain off the poles is open (`offPoles_isOpen`), so the recurrence holds on a whole neighborhood and may
be differentiated.  This carries the difference structure to the next polygamma order: iterating gives
`psi'(s+n) = psi'(s) - sum_{k<n} 1/(s+k)^(2 : ℕ)`, and the same telescoping-and-distinct-values argument shows
trigamma is transcendental -- the difference-side ladder extends to every polygamma. -/
theorem trigamma_recurrence (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) :
    deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) (s + 1)
      = deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s - 1 / s^(2 : ℕ) := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hs1 : ∀ p : ℕ, s + 1 ≠ -(p:ℂ) := by
    intro p h; exact hs (p+1) (by push_cast; linear_combination h)
  set ψ : ℂ → ℂ := fun z => deriv Complex.Gamma z / Complex.Gamma z with hψ
  have hψd : ∀ {x : ℂ}, (∀ p : ℕ, x ≠ -(p:ℂ)) → DifferentiableAt ℂ ψ x := by
    intro x hx
    exact ((analyticAt_Gamma x hx).deriv.differentiableAt).div
      (analyticAt_Gamma x hx).differentiableAt (Complex.Gamma_ne_zero hx)
  -- digamma recurrence holds on a neighborhood of s (off-poles is open)
  have hev : (fun z => ψ (z + 1)) =ᶠ[𝓝 s] (fun z => ψ z + 1 / z) := by
    filter_upwards [offPoles_isOpen.mem_nhds hs] with z hz
    exact digamma_recurrence z hz
  -- LHS derivative
  have hL : deriv (fun z => ψ (z + 1)) s = deriv ψ (s + 1) := by
    have hd : HasDerivAt (fun z : ℂ => z + 1) 1 s := (hasDerivAt_id s).add_const 1
    have hc := (hψd hs1).hasDerivAt.comp s hd
    have hfun : (fun z => ψ (z + 1)) = ψ ∘ fun z : ℂ => z + 1 := by
      funext z
      rfl
    rw [hfun]
    simpa only [mul_one] using hc.deriv
  -- RHS derivative
  have hR : deriv (fun z => ψ z + 1 / z) s = deriv ψ s - 1 / s^(2 : ℕ) := by
    have hinv : HasDerivAt (fun z : ℂ => 1 / z) (-1 / s ^ 2) s := by
      have h := hasDerivAt_inv hs0
      have e1 : (fun z : ℂ => 1 / z) = fun z => z⁻¹ := by funext z; rw [one_div]
      rw [e1, show (-1 / s ^ 2 : ℂ) = -(s ^ 2)⁻¹ by rw [neg_div, one_div]]
      exact h
    have hd : HasDerivAt (fun z => ψ z + 1 / z) (deriv ψ s + (-1 / s ^ 2)) s :=
      (hψd hs).hasDerivAt.add hinv
    rw [hd.deriv]; ring
  rw [← hL, hev.deriv_eq, hR]

/-- **Trigamma telescope and transcendence.**  `trigamma_telescope`: `psi'(s+n) = psi'(s) - sum_{k<n}
1/(s+k)^(2 : ℕ)`, iterating `trigamma_recurrence`.  `trigamma_transcendental`: `psi' = deriv(Gamma'/Gamma)` is
transcendental as a function -- at `s=1` the values `psi'(n+1) = psi'(1) - sum_{k<n} 1/(1+k)^(2 : ℕ)` are
strictly decreasing reals, hence pairwise distinct, so no nonzero polynomial vanishes on `psi'`.  The
digamma ladder (recurrence/telescope/transcendental) reproduced verbatim one polygamma order up, with the
same open-domain differentiation and distinct-values argument -- the difference side is a generative
ladder over all polygamma orders. -/
private theorem offp_natpos (a : ℕ) (ha : 1 ≤ a) : ∀ p : ℕ, (a:ℂ) ≠ -(p:ℂ) := by
  intro p h
  have hz : ((a + p : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
  have : a + p = 0 := by exact_mod_cast hz
  omega

theorem trigamma_telescope (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) (n : ℕ) :
    deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) (s + n)
      = deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
        - ∑ k ∈ Finset.range n, 1 / (s + (k:ℂ))^(2 : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : ∀ p : ℕ, s + (n:ℂ) ≠ -(p:ℂ) := by
      intro p h; exact hs (p + n) (by push_cast at h ⊢; linear_combination h)
    have hrec := trigamma_recurrence (s + (n:ℂ)) hsn
    rw [show s + ((n+1 : ℕ):ℂ) = (s + (n:ℂ)) + 1 by push_cast; ring, hrec, ih,
      Finset.sum_range_succ]
    ring

theorem trigamma_transcendental :
    ¬ ∃ P : Polynomial ℂ, P ≠ 0 ∧
      ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p:ℂ)) →
        P.eval (deriv (fun w => deriv Complex.Gamma w / Complex.Gamma w) z) = 0 := by
  rintro ⟨P, hP, hroot⟩
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  set hR : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, 1 / (1 + (k:ℝ))^(2 : ℕ) with hRdef
  have hmono : StrictMono hR := by
    apply strictMono_nat_of_lt_succ
    intro n; rw [hRdef]; simp only [Finset.sum_range_succ]
    have : (0:ℝ) < 1 / (1 + (n:ℝ))^(2 : ℕ) := by positivity
    linarith
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => deriv (fun w => deriv Complex.Gamma w / Complex.Gamma w) 1 - ((hR n : ℝ) : ℂ))
  · intro a b hab
    have h2 : ((hR a : ℝ) : ℂ) = ((hR b : ℝ) : ℂ) := by linear_combination -hab
    exact hmono.injective (Complex.ofReal_inj.mp h2)
  · intro n
    have hcast : ((hR n : ℝ) : ℂ) = ∑ k ∈ Finset.range n, 1 / (1 + (k:ℂ))^(2 : ℕ) := by
      rw [hRdef]; push_cast; ring
    have h1off : ∀ p : ℕ, (1:ℂ) ≠ -(p:ℂ) := by simpa using offp_natpos 1 (le_refl 1)
    have htel := trigamma_telescope 1 h1off n
    have hoff : ∀ p : ℕ, (1:ℂ) + (n:ℂ) ≠ -(p:ℂ) := by
      have := offp_natpos (n + 1) (by omega)
      intro p hp; exact this p (by push_cast at hp ⊢; linear_combination hp)
    have hr := hroot ((1:ℂ) + (n:ℂ)) hoff
    rw [hcast, ← htel]
    exact hr

/-- **The log-derivative of Γ is analytic off the poles**, and so is each of its iterated derivatives.
`analyticAt_logDeriv_Gamma`: `psi = Gamma'/Gamma` is analytic at every `x` off the poles (quotient of the
analytic `Gamma'` and `Gamma`, the latter nonzero there).  `analyticAt_iteratedDeriv_logDeriv`: hence
`psi^(m)` is analytic at each such `x` for every `m` (induction, `AnalyticAt.deriv`).  This is the
smoothness foundation for the polygamma difference ladder: every `psi^(m)` is differentiable off the
poles, so each recurrence `psi^(m)(s+1) - psi^(m)(s) = (-1)^m m!/s^(m+1)` may be differentiated to the
next order. -/
theorem analyticAt_logDeriv_Gamma (x : ℂ) (hx : ∀ p : ℕ, x ≠ -(p:ℂ)) :
    AnalyticAt ℂ (fun z => deriv Complex.Gamma z / Complex.Gamma z) x :=
  (analyticAt_Gamma x hx).deriv.div (analyticAt_Gamma x hx) (Complex.Gamma_ne_zero hx)

theorem analyticAt_iteratedDeriv_logDeriv (m : ℕ) (x : ℂ) (hx : ∀ p : ℕ, x ≠ -(p:ℂ)) :
    AnalyticAt ℂ (iteratedDeriv m (fun z => deriv Complex.Gamma z / Complex.Gamma z)) x := by
  induction m with
  | zero => simpa [iteratedDeriv_zero] using analyticAt_logDeriv_Gamma x hx
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

/-- **The general polygamma difference equation.**  For every order `m` and `s` off the poles,
`psi^(m)(s+1) - psi^(m)(s) = (-1)^m * m! / s^(m+1)` where `psi = Gamma'/Gamma`.  Proof by induction on `m`:
the base case is the digamma recurrence; the step differentiates the `m`-th recurrence -- valid because it
holds on the open off-poles set (`offPoles_isOpen`), with every `psi^(m)` differentiable there
(`analyticAt_iteratedDeriv_logDeriv`) -- using the shift rule for the left side and the power rule for the
right.  This is the whole polygamma difference ladder in one theorem: each order's integer values
`psi^(m)(n+1) = psi^(m)(1) + (-1)^m m! * sum 1/(1+k)^(m+1)` are strictly monotone, so every polygamma is
transcendental as a function -- the shift-side obstruction, uniform over all orders. -/
theorem polygamma_recurrence (m : ℕ) : ∀ s : ℂ, (∀ p : ℕ, s ≠ -(p:ℂ)) →
    iteratedDeriv m (fun z => deriv Complex.Gamma z / Complex.Gamma z) (s + 1)
      - iteratedDeriv m (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
      = (-1)^m * (m.factorial : ℂ) / s^(m+1) := by
  induction m with
  | zero =>
    intro s hs
    have hd := digamma_recurrence s hs
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    linear_combination hd
  | succ m ih =>
    intro s hs
    have hs0 : s ≠ 0 := by simpa using hs 0
    have hs1 : ∀ p : ℕ, s + 1 ≠ -(p:ℂ) := by
      intro p h; exact hs (p+1) (by push_cast; linear_combination h)
    set ψ : ℂ → ℂ := fun z => deriv Complex.Gamma z / Complex.Gamma z with hψ
    have hev : (fun z => iteratedDeriv m ψ (z + 1) - iteratedDeriv m ψ z)
        =ᶠ[𝓝 s] (fun z => (-1)^m * (m.factorial : ℂ) / z^(m+1)) := by
      filter_upwards [offPoles_isOpen.mem_nhds hs] with z hz
      exact ih z hz
    have hLdiff : DifferentiableAt ℂ (iteratedDeriv m ψ) s :=
      (analyticAt_iteratedDeriv_logDeriv m s hs).differentiableAt
    have hL1diff : DifferentiableAt ℂ (iteratedDeriv m ψ) (s + 1) :=
      (analyticAt_iteratedDeriv_logDeriv m (s + 1) hs1).differentiableAt
    have hshiftderiv : deriv (fun z => iteratedDeriv m ψ (z + 1)) s
        = iteratedDeriv (m+1) ψ (s + 1) := by
      have h := (hL1diff.hasDerivAt.comp s ((hasDerivAt_id s).add_const 1)).deriv
      simp only [Function.comp_def, id_eq] at h
      rw [h, mul_one, iteratedDeriv_succ]
    have hfdiff : DifferentiableAt ℂ (fun z => iteratedDeriv m ψ (z + 1)) s := by
      have h := (hL1diff.comp s ((differentiableAt_id).add_const 1))
      simpa [Function.comp_def] using h
    have hLderiv : deriv (fun z => iteratedDeriv m ψ (z + 1) - iteratedDeriv m ψ z) s
        = iteratedDeriv (m+1) ψ (s + 1) - iteratedDeriv (m+1) ψ s := by
      show deriv ((fun z => iteratedDeriv m ψ (z + 1)) - iteratedDeriv m ψ) s = _
      rw [deriv_sub hfdiff hLdiff, hshiftderiv, ← iteratedDeriv_succ]
    have hRderiv : deriv (fun z => (-1)^m * (m.factorial : ℂ) / z^(m+1)) s
        = (-1)^(m+1) * ((m+1).factorial : ℂ) / s^(m+2) := by
      have hz : HasDerivAt (fun z : ℂ => z^(m+1)) ((↑(m+1)) * s^m) s := by
        simpa using hasDerivAt_pow (m+1) s
      have hden := (hasDerivAt_const s ((-1)^m * (m.factorial : ℂ))).div hz (pow_ne_zero _ hs0)
      show deriv ((fun _ : ℂ => (-1)^m * (m.factorial : ℂ)) / fun z => z^(m+1)) s = _
      rw [hden.deriv]
      have hsm : s ≠ 0 := hs0
      field_simp
      push_cast [Nat.factorial_succ]
      ring
    calc iteratedDeriv (m+1) ψ (s + 1) - iteratedDeriv (m+1) ψ s
        = deriv (fun z => iteratedDeriv m ψ (z + 1) - iteratedDeriv m ψ z) s := hLderiv.symm
      _ = deriv (fun z => (-1)^m * (m.factorial : ℂ) / z^(m+1)) s := hev.deriv_eq
      _ = (-1)^(m+1) * ((m+1).factorial : ℂ) / s^(m+2) := hRderiv

/-- **Every polygamma is transcendental as a function** (general order).  `polygamma_telescope`:
`psi^(m)(s+n) = psi^(m)(s) + (-1)^m m! * sum_{k<n} 1/(s+k)^(m+1)`, iterating `polygamma_recurrence`.
`polygamma_transcendental (m)`: no nonzero polynomial vanishes on `psi^(m) = iteratedDeriv m (Gamma'/Gamma)`
off the poles -- at `s=1` the values `psi^(m)(n+1) = psi^(m)(1) + (-1)^m m! * H_n^(m+1)` (with `H_n^(m+1)` the
strictly-monotone generalized-harmonic partial sums, scaled by the nonzero `(-1)^m m!`) are pairwise
distinct, so `P` would have infinitely many roots.  The entire shift-side obstruction, uniform over all
infinitely many polygamma orders in one pair of theorems -- the difference-side ladder complete. -/
private theorem offp_pos (a : ℕ) (ha : 1 ≤ a) : ∀ p : ℕ, (a:ℂ) ≠ -(p:ℂ) := by
  intro p h
  have hz : ((a + p : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
  have : a + p = 0 := by exact_mod_cast hz
  omega

theorem polygamma_telescope (m : ℕ) (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) (n : ℕ) :
    iteratedDeriv m (fun z => deriv Complex.Gamma z / Complex.Gamma z) (s + n)
      = iteratedDeriv m (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
        + (-1)^m * (m.factorial : ℂ) * ∑ k ∈ Finset.range n, 1 / (s + (k:ℂ))^(m+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : ∀ p : ℕ, s + (n:ℂ) ≠ -(p:ℂ) := by
      intro p h; exact hs (p + n) (by push_cast at h ⊢; linear_combination h)
    have hrec := polygamma_recurrence m (s + (n:ℂ)) hsn
    rw [show s + ((n+1 : ℕ):ℂ) = (s + (n:ℂ)) + 1 by push_cast; ring]
    have hstep : iteratedDeriv m (fun z => deriv Complex.Gamma z / Complex.Gamma z) ((s + (n:ℂ)) + 1)
        = iteratedDeriv m (fun z => deriv Complex.Gamma z / Complex.Gamma z) (s + (n:ℂ))
          + (-1)^m * (m.factorial : ℂ) / (s + (n:ℂ))^(m+1) := by linear_combination hrec
    rw [hstep, ih, Finset.sum_range_succ]
    ring

theorem polygamma_transcendental (m : ℕ) :
    ¬ ∃ P : Polynomial ℂ, P ≠ 0 ∧
      ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p:ℂ)) →
        P.eval (iteratedDeriv m (fun w => deriv Complex.Gamma w / Complex.Gamma w) z) = 0 := by
  rintro ⟨P, hP, hroot⟩
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  set c : ℂ := (-1)^m * (m.factorial : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero (pow_ne_zero m (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero m)
  set hR : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, 1 / (1 + (k:ℝ))^(m+1) with hRdef
  have hmono : StrictMono hR := by
    apply strictMono_nat_of_lt_succ
    intro n; rw [hRdef]; simp only [Finset.sum_range_succ]
    have : (0:ℝ) < 1 / (1 + (n:ℝ))^(m+1) := by positivity
    linarith
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => iteratedDeriv m (fun w => deriv Complex.Gamma w / Complex.Gamma w) 1
      + c * ((hR n : ℝ) : ℂ))
  · intro a b hab
    have h2 : c * ((hR a : ℝ) : ℂ) = c * ((hR b : ℝ) : ℂ) := by linear_combination hab
    have h3 : ((hR a : ℝ) : ℂ) = ((hR b : ℝ) : ℂ) := mul_left_cancel₀ hcne h2
    exact hmono.injective (Complex.ofReal_inj.mp h3)
  · intro n
    have hcast : c * ((hR n : ℝ) : ℂ)
        = c * ∑ k ∈ Finset.range n, 1 / (1 + (k:ℂ))^(m+1) := by
      rw [hRdef]; push_cast; ring
    have h1off : ∀ p : ℕ, (1:ℂ) ≠ -(p:ℂ) := by simpa using offp_pos 1 (le_refl 1)
    have htel := polygamma_telescope m 1 h1off n
    have hoff : ∀ p : ℕ, (1:ℂ) + (n:ℂ) ≠ -(p:ℂ) := by
      have := offp_pos (n + 1) (by omega)
      intro p hp; exact this p (by push_cast at hp ⊢; linear_combination hp)
    have hr := hroot ((1:ℂ) + (n:ℂ)) hoff
    rw [hcast, hc, ← htel]
    exact hr

/-- **`Gamma'' = Gamma * (psi^(2 : ℕ) + psi')`** off the poles, for the log-derivative `psi = Gamma'/Gamma`.
The order-2 Bell identity: the second derivative of `Gamma` equals `Gamma` times a polynomial in the
`psi`-jet `(psi, psi')`.  Immediate from the log-derivative identity `Gamma''*Gamma - (Gamma')^(2 : ℕ) =
Gamma^(2 : ℕ)*psi'` (`gamma_secondDeriv_logDeriv_identity`) after dividing by `Gamma`.  This is the order-2 rung
of the Bell chain `Gamma^(n) = Gamma * B_n(psi, ..., psi^(n-1))` that expresses every derivative of `Gamma`
through its log-derivative jet -- the concrete engine of the reduction `Gamma differentially algebraic ==>
psi differentially algebraic`, the link from the differential side to the (complete) difference side. -/
theorem iteratedDeriv_two_Gamma_eq_logDeriv (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) :
    iteratedDeriv 2 Complex.Gamma s
      = Complex.Gamma s * ((deriv Complex.Gamma s / Complex.Gamma s)^(2 : ℕ)
        + deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s) := by
  have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have h1 : DifferentiableAt ℂ Complex.Gamma s := (analyticAt_Gamma s hs).differentiableAt
  have h2 : DifferentiableAt ℂ (deriv Complex.Gamma) s := (analyticAt_Gamma s hs).deriv.differentiableAt
  have hid := gamma_secondDeriv_logDeriv_identity s hne h1 h2
  field_simp
  linear_combination hid

/-- **`Gamma''' = Gamma * (psi^(3 : ℕ) + 3 psi psi' + psi'')`** off the poles -- the order-3 Bell identity.
Obtained by differentiating the order-2 identity `Gamma'' = Gamma*(psi^(2 : ℕ) + psi')` on the open off-poles
set (`offPoles_isOpen`), with `Gamma`, `psi`, `psi'` differentiable there (`analyticAt_Gamma`,
`analyticAt_logDeriv_Gamma`): `(Gamma*(psi^(2 : ℕ)+psi'))' = Gamma'*(psi^(2 : ℕ)+psi') + Gamma*(2 psi psi' + psi'') =
Gamma*(psi*(psi^(2 : ℕ)+psi') + 2 psi psi' + psi'') = Gamma*(psi^(3 : ℕ) + 3 psi psi' + psi'')`, using `Gamma' =
Gamma*psi`.  Third rung of the Bell chain `Gamma^(n) = Gamma * B_n(psi-jet)`, differentiated exactly as the
polygamma recurrences were -- each derivative of `Gamma` is `Gamma` times a polynomial in the log-derivative
jet, the concrete substitution behind `Gamma differentially algebraic ==> psi differentially algebraic`. -/
theorem iteratedDeriv_three_Gamma_eq_logDeriv (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) :
    iteratedDeriv 3 Complex.Gamma s
      = Complex.Gamma s * ((deriv Complex.Gamma s / Complex.Gamma s)^(3 : ℕ)
        + 3 * (deriv Complex.Gamma s / Complex.Gamma s)
            * deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
        + deriv (deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z)) s) := by
  set ψ : ℂ → ℂ := fun z => deriv Complex.Gamma z / Complex.Gamma z with hψdef
  -- order-2 identity holds on the open off-poles set
  have hev : (iteratedDeriv 2 Complex.Gamma)
      =ᶠ[𝓝 s] (fun z => Complex.Gamma z * (ψ z ^ 2 + deriv ψ z)) := by
    filter_upwards [offPoles_isOpen.mem_nhds hs] with z hz
    exact iteratedDeriv_two_Gamma_eq_logDeriv z hz
  have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
    (analyticAt_Gamma s hs).differentiableAt.hasDerivAt
  have hψ : HasDerivAt ψ (deriv ψ s) s :=
    (analyticAt_logDeriv_Gamma s hs).differentiableAt.hasDerivAt
  have hψ' : HasDerivAt (deriv ψ) (deriv (deriv ψ) s) s :=
    (analyticAt_logDeriv_Gamma s hs).deriv.differentiableAt.hasDerivAt
  have hG : HasDerivAt (fun z => ψ z ^ 2 + deriv ψ z)
      (2 * ψ s ^ 1 * deriv ψ s + deriv (deriv ψ) s) s :=
    (hψ.pow 2).add hψ'
  have hRHS : HasDerivAt (fun z => Complex.Gamma z * (ψ z ^ 2 + deriv ψ z))
      (deriv Complex.Gamma s * (ψ s ^ 2 + deriv ψ s)
        + Complex.Gamma s * (2 * ψ s ^ 1 * deriv ψ s + deriv (deriv ψ) s)) s :=
    hΓ.mul hG
  have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hkey : iteratedDeriv 3 Complex.Gamma s
      = deriv Complex.Gamma s * (ψ s ^ 2 + deriv ψ s)
        + Complex.Gamma s * (2 * ψ s ^ 1 * deriv ψ s + deriv (deriv ψ) s) := by
    rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ]
    rw [hev.deriv_eq, hRHS.deriv]
  rw [hkey, hψdef]
  field_simp
  ring

/-- **`Gamma^(4) = Gamma * (psi^(4 : ℕ) + 6 psi^(2 : ℕ) psi' + 3 psi'^(2 : ℕ) + 4 psi psi'' + psi''')`** off the poles --
the order-4 Bell identity, by differentiating the order-3 identity on the open off-poles set
(`offPoles_isOpen`), the `psi`-jet differentiable via `analyticAt_logDeriv_Gamma`.  Fourth rung of the Bell
chain `Gamma^(n) = Gamma * B_n(psi-jet)`; the coefficients `1; 6,3,4; 1` are the complete Bell/Faa-di-Bruno
numbers.  Each rung differentiates to the next by the fixed pattern (`HasDerivAt` product rule on the open
domain), so the chain is uniform and self-propagating -- the substitution engine of
`Gamma differentially algebraic ==> psi differentially algebraic`. -/
theorem iteratedDeriv_four_Gamma_eq_logDeriv (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) :
    iteratedDeriv 4 Complex.Gamma s
      = Complex.Gamma s * ((deriv Complex.Gamma s / Complex.Gamma s)^(4 : ℕ)
        + 6 * (deriv Complex.Gamma s / Complex.Gamma s)^(2 : ℕ)
            * deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
        + 3 * (deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s)^(2 : ℕ)
        + 4 * (deriv Complex.Gamma s / Complex.Gamma s)
            * deriv (deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z)) s
        + deriv (deriv (deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z))) s) := by
  set ψ : ℂ → ℂ := fun z => deriv Complex.Gamma z / Complex.Gamma z with hψdef
  have hev : (iteratedDeriv 3 Complex.Gamma)
      =ᶠ[𝓝 s] (fun z => Complex.Gamma z * (ψ z ^ 3 + 3 * (ψ z * deriv ψ z) + deriv (deriv ψ) z)) := by
    filter_upwards [offPoles_isOpen.mem_nhds hs] with z hz
    have := iteratedDeriv_three_Gamma_eq_logDeriv z hz
    rw [hψdef]; linear_combination this
  have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
    (analyticAt_Gamma s hs).differentiableAt.hasDerivAt
  have hψ : HasDerivAt ψ (deriv ψ s) s :=
    (analyticAt_logDeriv_Gamma s hs).differentiableAt.hasDerivAt
  have hψ1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) s) s :=
    (analyticAt_logDeriv_Gamma s hs).deriv.differentiableAt.hasDerivAt
  have hψ2 : HasDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) s) s :=
    (analyticAt_logDeriv_Gamma s hs).deriv.deriv.differentiableAt.hasDerivAt
  have hB : HasDerivAt (fun z => ψ z ^ 3 + 3 * (ψ z * deriv ψ z) + deriv (deriv ψ) z)
      (3 * ψ s ^ 2 * deriv ψ s
        + 3 * (deriv ψ s * deriv ψ s + ψ s * deriv (deriv ψ) s)
        + deriv (deriv (deriv ψ)) s) s :=
    ((hψ.pow 3).add ((hψ.mul hψ1).const_mul 3)).add hψ2
  have hkey : iteratedDeriv 4 Complex.Gamma s
      = deriv Complex.Gamma s * (ψ s ^ 3 + 3 * (ψ s * deriv ψ s) + deriv (deriv ψ) s)
        + Complex.Gamma s * (3 * ψ s ^ 2 * deriv ψ s
          + 3 * (deriv ψ s * deriv ψ s + ψ s * deriv (deriv ψ) s)
          + deriv (deriv (deriv ψ)) s) := by
    rw [show (4:ℕ) = 3 + 1 from rfl, iteratedDeriv_succ]
    exact hev.deriv_eq.trans (hΓ.mul hB).deriv
  rw [hkey, hψdef]
  have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  field_simp
  ring

/-- **The reciprocal Gamma `1/Gamma` is transcendental as a function.**  No nonzero polynomial vanishes
on `z |-> (Gamma z)^{-1}`.  Since `Gamma(n+2) = (n+1)!`, the values `(Gamma(n+2))^{-1} = 1/(n+1)!` are
infinitely many distinct reciprocals of factorials, so such a `P` would have infinitely many roots.
Unlike `Gamma`, the reciprocal `1/Gamma` is *entire* (no poles), so this is transcendence of an entire
function -- the value-side companion to `gamma_transcendental`, on the everywhere-defined side. -/
theorem oneDivGamma_transcendental :
    ¬ ∃ P : Polynomial ℂ, P ≠ 0 ∧ ∀ z : ℂ, P.eval (Complex.Gamma z)⁻¹ = 0 := by
  rintro ⟨P, hP, hroot⟩
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((n + 1).factorial : ℂ))⁻¹)
  · intro a b hab
    have h : (((a + 1).factorial : ℂ))⁻¹ = (((b + 1).factorial : ℂ))⁻¹ := hab
    have hane : ((a + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a+1)
    have hbne : ((b + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (b+1)
    have hfe : ((a + 1).factorial : ℂ) = ((b + 1).factorial : ℂ) := by
      rw [inv_inj] at h; exact h
    have hnat : (a + 1).factorial = (b + 1).factorial := by exact_mod_cast hfe
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd hnat (by have := Nat.factorial_lt (n := a+1) (m := b+1) (by omega); omega)
    · exact heq
    · exact absurd hnat.symm (by have := Nat.factorial_lt (n := b+1) (m := a+1) (by omega); omega)
  · intro n
    have hg : Complex.Gamma ((n:ℂ) + 1 + 1) = ((n + 1).factorial : ℂ) := by
      have h := Complex.Gamma_nat_eq_factorial (n + 1)
      push_cast at h
      convert h using 2
    have hr := hroot ((n:ℂ) + 1 + 1)
    rw [hg] at hr
    exact hr

/-- **Chain rule for a multivariate polynomial evaluated along a jet.**  For `Q : MvPolynomial (Fin n) C`
and differentiable coordinate functions `g_j` with `HasDerivAt (g j) (g' j) x`, the map
`s |-> eval (fun j => g j s) Q` has derivative `sum_j eval (fun j => g j x) (pderiv j Q) * g' j` at `x`.
Proved by `MvPolynomial.induction_on`: constants have zero derivative, sums add, and the `p * X_i` step is
the product rule combined with `pderiv (p * X_i) = pderiv p * X_i + p * (delta at i)`.  This is the
analytic engine for the general Bell chain `Gamma^(n) = Gamma * B_n(psi-jet)`: differentiating
`Gamma * eval(psi-jet)(B_n)` needs exactly this eval-along-a-jet chain rule, so with it the Bell recurrence
`B_{n+1} = X_0 * B_n + sum_j (pderiv j B_n) * X_{j+1}` closes by induction -- the missing piece of
`Gamma differentially algebraic ==> psi differentially algebraic`. -/
theorem hasDerivAt_mvEval_jet {n : ℕ} (Q : MvPolynomial (Fin n) ℂ)
    (g : Fin n → ℂ → ℂ) (g' : Fin n → ℂ) (x : ℂ) (hg : ∀ j, HasDerivAt (g j) (g' j) x) :
    HasDerivAt (fun s => MvPolynomial.eval (fun j => g j s) Q)
      (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j Q) * g' j) x := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have hcf : (fun s => MvPolynomial.eval (fun j => g j s) (MvPolynomial.C a)) = fun _ => a := by
      funext s; simp
    rw [hcf]
    simp only [MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact hasDerivAt_const x a
  | add p q hp hq =>
    have hf : (fun s => MvPolynomial.eval (fun j => g j s) (p + q))
        = (fun s => MvPolynomial.eval (fun j => g j s) p) +
            fun s => MvPolynomial.eval (fun j => g j s) q := by
      funext s; simp
    rw [hf]
    have hcoef :
        (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j (p + q)) * g' j) =
          (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j p) * g' j) +
            ∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j q) * g' j := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]
    rw [hcoef]
    exact hp.add hq
  | mul_X p i hp =>
    have hfun : (fun s => MvPolynomial.eval (fun j => g j s) (p * MvPolynomial.X i))
        = (fun s => MvPolynomial.eval (fun j => g j s) p) * g i := by
      funext s; simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    rw [hfun]
    have hcoef :
        (∑ j, MvPolynomial.eval (fun j => g j x)
            (MvPolynomial.pderiv j (p * MvPolynomial.X i)) * g' j) =
          (∑ j, MvPolynomial.eval (fun j => g j x) (MvPolynomial.pderiv j p) * g' j) *
              g i x +
            MvPolynomial.eval (fun j => g j x) p * g' i := by
      simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, MvPolynomial.pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero,
        add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      · rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Ne.symm hj]
        · intro h; simp at h
    rw [hcoef]
    exact hp.mul (hg i)

/-- **The general Bell chain: every derivative of Gamma is Gamma times a polynomial in the log-derivative
jet.**  For every `n` there is a polynomial `B : MvPolynomial (Fin n) C` with
`Gamma^(n)(s) = Gamma(s) * eval (fun j => psi^(j)(s)) B` off the poles, `psi = Gamma'/Gamma`.  By induction:
`B_0 = 1`; the step differentiates `Gamma * eval(psi-jet)(B_n)` on the open off-poles set, using
`Gamma' = Gamma*psi` and the eval-along-a-jet chain rule (`hasDerivAt_mvEval_jet`), yielding the Bell
recurrence `B_{n+1} = X_0 * (rename B_n) + sum_j (rename (pderiv j B_n)) * X_{j+1}`.  This is the concrete
content of `Gamma differentially algebraic ==> psi differentially algebraic`: the differential field of
`Gamma` over `C(s)` is generated, over `Gamma`, by the `psi`-jet -- so any algebraic differential relation
for `Gamma`, after substituting these identities and using that `Gamma` is transcendental, descends to a
differential relation for `psi`.  The bridge from the differential side to the (complete) difference side. -/
theorem exists_gamma_bell (n : ℕ) :
    ∃ B : MvPolynomial (Fin n) ℂ, ∀ s : ℂ, (∀ p : ℕ, s ≠ -(p:ℂ)) →
      iteratedDeriv n Complex.Gamma s
        = Complex.Gamma s * MvPolynomial.eval
            (fun j : Fin n => iteratedDeriv (j:ℕ) (fun z => deriv Complex.Gamma z / Complex.Gamma z) s) B := by
  induction n with
  | zero => exact ⟨1, fun s hs => by simp [iteratedDeriv_zero]⟩
  | succ n ih =>
    obtain ⟨Bn, hBn⟩ := ih
    set ψ : ℂ → ℂ := fun z => deriv Complex.Gamma z / Complex.Gamma z with hψdef
    refine ⟨MvPolynomial.X 0 * MvPolynomial.rename Fin.castSucc Bn
      + ∑ j : Fin n, MvPolynomial.rename Fin.castSucc (MvPolynomial.pderiv j Bn)
          * MvPolynomial.X j.succ, fun s hs => ?_⟩
    -- differentiate the IH on the open off-poles set
    have hev : (iteratedDeriv n Complex.Gamma)
        =ᶠ[𝓝 s] (fun w => Complex.Gamma w * MvPolynomial.eval
            (fun j : Fin n => iteratedDeriv (j:ℕ) ψ w) Bn) := by
      filter_upwards [offPoles_isOpen.mem_nhds hs] with w hw
      rw [hψdef]; exact hBn w hw
    have hg : ∀ j : Fin n, HasDerivAt (fun w => iteratedDeriv (j:ℕ) ψ w)
        (iteratedDeriv ((j:ℕ)+1) ψ s) s := by
      intro j
      have := (analyticAt_iteratedDeriv_logDeriv (j:ℕ) s hs).differentiableAt.hasDerivAt
      rw [hψdef]; rw [iteratedDeriv_succ]; exact this
    have hchain := hasDerivAt_mvEval_jet Bn (fun j => fun w => iteratedDeriv (j:ℕ) ψ w)
      (fun j => iteratedDeriv ((j:ℕ)+1) ψ s) s hg
    have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
      (analyticAt_Gamma s hs).differentiableAt.hasDerivAt
    have hRHS := hΓ.mul hchain
    have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
    have hgpsi : deriv Complex.Gamma s = Complex.Gamma s * ψ s := by
      rw [hψdef]; field_simp
    rw [iteratedDeriv_succ, hev.deriv_eq.trans hRHS.deriv, hgpsi]
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def, Fin.val_succ,
      Fin.val_castSucc, iteratedDeriv_zero, Fin.val_zero]
    ring

/-- **The log-derivative-jet form of the Bell chain.**  Off the poles, `Gamma^(n)/Gamma` is a polynomial
in the log-derivative jet `(psi, psi', ..., psi^(n-1))` with `psi = Gamma'/Gamma`: there is
`B : MvPolynomial (Fin n) C` with `Gamma^(n)(s)/Gamma(s) = eval (fun j => psi^(j)(s)) B`.  Immediate from
`exists_gamma_bell` by dividing by `Gamma` (nonzero off the poles).  This is the exact expression a
differential-algebra transfer consumes: `Gamma^(k)` normalized by `Gamma` lies in `C(s)[psi-jet]`, so the
differential field of `Gamma` is `C(s)(Gamma, psi-jet)` -- the step that turns any relation on `Gamma`'s
derivative jet into one on the `psi`-jet (using that `Gamma` is transcendental). -/
theorem gamma_iteratedDeriv_div_eq_bell (n : ℕ) :
    ∃ B : MvPolynomial (Fin n) ℂ, ∀ s : ℂ, (∀ p : ℕ, s ≠ -(p:ℂ)) →
      iteratedDeriv n Complex.Gamma s / Complex.Gamma s
        = MvPolynomial.eval
            (fun j : Fin n => iteratedDeriv (j:ℕ) (fun z => deriv Complex.Gamma z / Complex.Gamma z) s) B := by
  obtain ⟨B, hB⟩ := exists_gamma_bell n
  refine ⟨B, fun s hs => ?_⟩
  rw [hB s hs, mul_comm, mul_div_assoc, div_self (Complex.Gamma_ne_zero hs), mul_one]

/-- **The log-derivative's derivative lies in `C(s)(Gamma-jet)` -- the converse inclusion, first rung.**
Off the poles, `psi' = eval (fun j => Gamma^(j)) (X_2 X_0 - X_1^(2 : ℕ)) / Gamma^(2 : ℕ)`, i.e.
`psi'(s) = (Gamma''(s) Gamma(s) - Gamma'(s)^(2 : ℕ))/Gamma(s)^(2 : ℕ)` -- a rational function of the `Gamma`-jet.
Immediate from `gamma_secondDeriv_logDeriv_identity`.  Where the Bell chain shows `Gamma^(k) in
Gamma * C(s)[psi-jet]` (forward), this shows `psi^(k) in C(s)(Gamma-jet)` (converse), here for `k=1`.
Together the two inclusions give `C(s)<Gamma> = C(s)(Gamma, psi-jet)`: the differential fields of `Gamma`
and of its log-derivative `psi` coincide over `Gamma`, so `Gamma` DA and `psi` DA are equivalent -- the
field equality underlying the transfer. -/
theorem logDeriv_deriv_eq_gammaJet :
    ∃ N : MvPolynomial (Fin 3) ℂ, ∀ s : ℂ, (∀ p : ℕ, s ≠ -(p:ℂ)) →
      deriv (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
        = MvPolynomial.eval (fun j : Fin 3 => iteratedDeriv (j:ℕ) Complex.Gamma s) N
            / (Complex.Gamma s)^(2 : ℕ) := by
  refine ⟨MvPolynomial.X 2 * MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2, fun s hs => ?_⟩
  have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have h1 : DifferentiableAt ℂ Complex.Gamma s := (analyticAt_Gamma s hs).differentiableAt
  have h2 : DifferentiableAt ℂ (deriv Complex.Gamma) s := (analyticAt_Gamma s hs).deriv.differentiableAt
  have hid := gamma_secondDeriv_logDeriv_identity s hne h1 h2
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, show ((0:Fin 3):ℕ) = 0 from rfl, show ((1:Fin 3):ℕ) = 1 from rfl,
    show ((2:Fin 3):ℕ) = 2 from rfl, iteratedDeriv_zero, iteratedDeriv_one]
  rw [eq_div_iff (pow_ne_zero 2 hne)]
  linear_combination -hid

/-- **The general converse Bell chain: every log-derivative in `C(s)(Gamma-jet)`.**  For each `k` there is
`N : MvPolynomial (Fin (k+2)) C` with `psi^(k)(s) = eval (fun j => Gamma^(j)(s)) N / Gamma(s)^(k+1)` off the
poles, `psi = Gamma'/Gamma`.  By induction: `psi = Gamma'/Gamma` (N = X_1); the step differentiates
`eval(Gamma-jet)(N_k)/Gamma^(k+1)` on the open off-poles set via the quotient rule and the eval-jet chain
rule (`hasDerivAt_mvEval_jet`), giving the converse recurrence `N_{k+1} = (sum_j (rename pderiv_j N_k)*
X_{j+1})*X_0 - (k+1)*(rename N_k)*X_1`.  This is the converse of `exists_gamma_bell`: together they give
`Gamma^(k) in Gamma*C(s)[psi-jet]` and `psi^(k) in C(s)(Gamma-jet)`, hence the differential-field equality
`C(s)<Gamma> = C(s)(Gamma, psi-jet)`.  So `Gamma` is differentially algebraic iff `psi` is -- the complete
field content of `Gamma DA <=> psi DA`, the bridge between the differential and difference sides. -/
private theorem analyticAt_itDeriv_Gamma (m : ℕ) (x : ℂ) (hx : ∀ p : ℕ, x ≠ -(p:ℂ)) :
    AnalyticAt ℂ (iteratedDeriv m Complex.Gamma) x := by
  induction m with
  | zero => simpa [iteratedDeriv_zero] using analyticAt_Gamma x hx
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem exists_logDeriv_bell (k : ℕ) :
    ∃ N : MvPolynomial (Fin (k+2)) ℂ, ∀ s : ℂ, (∀ p : ℕ, s ≠ -(p:ℂ)) →
      iteratedDeriv k (fun z => deriv Complex.Gamma z / Complex.Gamma z) s
        = MvPolynomial.eval (fun j : Fin (k+2) => iteratedDeriv (j:ℕ) Complex.Gamma s) N
            / (Complex.Gamma s)^(k+1) := by
  induction k with
  | zero =>
    refine ⟨MvPolynomial.X 1, fun s hs => ?_⟩
    simp [iteratedDeriv_zero, MvPolynomial.eval_X, iteratedDeriv_one]
  | succ k ih =>
    obtain ⟨Nk, hNk⟩ := ih
    refine ⟨(∑ j : Fin (k+2), MvPolynomial.rename Fin.castSucc (MvPolynomial.pderiv j Nk)
          * MvPolynomial.X j.succ) * MvPolynomial.X 0
        - MvPolynomial.C ((k:ℂ)+1) * MvPolynomial.rename Fin.castSucc Nk * MvPolynomial.X 1,
        fun s hs => ?_⟩
    set ψ : ℂ → ℂ := fun z => deriv Complex.Gamma z / Complex.Gamma z with hψdef
    have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
    have hev : (iteratedDeriv k ψ)
        =ᶠ[𝓝 s] (fun w => MvPolynomial.eval (fun j : Fin (k+2) => iteratedDeriv (j:ℕ) Complex.Gamma w) Nk
            / (Complex.Gamma w)^(k+1)) := by
      filter_upwards [offPoles_isOpen.mem_nhds hs] with w hw
      rw [hψdef]; exact hNk w hw
    have hg : ∀ j : Fin (k+2), HasDerivAt (fun w => iteratedDeriv (j:ℕ) Complex.Gamma w)
        (iteratedDeriv ((j:ℕ)+1) Complex.Gamma s) s := by
      intro j
      have := (analyticAt_itDeriv_Gamma (j:ℕ) s hs).differentiableAt.hasDerivAt
      rw [iteratedDeriv_succ]; exact this
    have hnum := hasDerivAt_mvEval_jet Nk (fun j => fun w => iteratedDeriv (j:ℕ) Complex.Gamma w)
      (fun j => iteratedDeriv ((j:ℕ)+1) Complex.Gamma s) s hg
    have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
      (analyticAt_Gamma s hs).differentiableAt.hasDerivAt
    have hden : HasDerivAt (fun w => (Complex.Gamma w)^(k+1))
        ((↑(k+1)) * (Complex.Gamma s)^k * deriv Complex.Gamma s) s := by
      have hfun :
          (fun w => (Complex.Gamma w) ^ (k + 1)) = Complex.Gamma ^ (k + 1) := by
        funext w
        rfl
      rw [hfun]
      exact hΓ.pow (k + 1)
    have hquot := hnum.div hden (pow_ne_zero (k+1) hne)
    rw [iteratedDeriv_succ, hev.deriv_eq.trans hquot.deriv]
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def,
      Fin.val_succ, Fin.val_castSucc, iteratedDeriv_zero, Fin.val_zero,
      show ((1 : Fin (k+3)):ℕ) = 1 from rfl, iteratedDeriv_one]
    rw [div_eq_div_iff (pow_ne_zero _ (pow_ne_zero (k+1) hne)) (pow_ne_zero (k+2) hne)]
    push_cast
    ring

/-- **Denominator-free form of the converse Bell chain.**  For each `k`, off the poles,
`psi^(k)(s) * Gamma(s)^(k+1) = eval (fun j => Gamma^(j)(s)) N` for some `N : MvPolynomial (Fin (k+2)) C` --
the polynomial identity relating the log-derivative jet to the `Gamma`-jet with no division (clearing the
`Gamma^(k+1)` denominator of `exists_logDeriv_bell`).  This is the shape a differential-elimination step
consumes: each `psi^(k)` is `Gamma^(-(k+1))` times a `Gamma`-jet polynomial, so given a differential
relation for `Gamma`, the `psi`-jet entries are all rational in a field of finite transcendence degree over
`C(s)`, forcing algebraic dependence among `psi, psi', ...` -- i.e. `psi` differentially algebraic.  The
algebraic content of `Gamma DA ==> psi DA`; the remaining step is the transcendence-degree count. -/
theorem logDeriv_mul_gammaPow_eq_gammaJet (k : ℕ) :
    ∃ N : MvPolynomial (Fin (k+2)) ℂ, ∀ s : ℂ, (∀ p : ℕ, s ≠ -(p:ℂ)) →
      iteratedDeriv k (fun z => deriv Complex.Gamma z / Complex.Gamma z) s * (Complex.Gamma s)^(k+1)
        = MvPolynomial.eval (fun j : Fin (k+2) => iteratedDeriv (j:ℕ) Complex.Gamma s) N := by
  obtain ⟨N, hN⟩ := exists_logDeriv_bell k
  refine ⟨N, fun s hs => ?_⟩
  rw [hN s hs, div_mul_cancel₀ _ (pow_ne_zero (k+1) (Complex.Gamma_ne_zero hs))]

/-- **The log-derivative of the reciprocal Gamma is minus the digamma.**  Off the poles,
`(1/Gamma)'/(1/Gamma) = -(Gamma'/Gamma) = -psi`.  Immediate from the derivative of the inverse.  This ties
the two completed sides together: `1/Gamma` is entire and transcendental (`oneDivGamma_transcendental`,
value side), and its logarithmic derivative is `-psi`, whose difference structure (`digamma_recurrence`,
`polygamma_*`) is the complete shift side.  So the entire function `1/Gamma` carries the same
difference-side obstruction as `Gamma`, with the sign flipped -- the reciprocal and the function share one
log-derivative up to sign, hence one hypertranscendence. -/
theorem oneDivGamma_logDeriv_eq_neg_digamma (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) :
    deriv (fun z => (Complex.Gamma z)⁻¹) s / (Complex.Gamma s)⁻¹
      = -(deriv Complex.Gamma s / Complex.Gamma s) := by
  have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hd : DifferentiableAt ℂ Complex.Gamma s := (analyticAt_Gamma s hs).differentiableAt
  have h : HasDerivAt (fun z => (Complex.Gamma z)⁻¹)
      (-deriv Complex.Gamma s / (Complex.Gamma s)^(2 : ℕ)) s := hd.hasDerivAt.inv hne
  rw [h.deriv]
  field_simp

/-- **The derivative of the reciprocal Gamma.**  Off the poles, `(1/Gamma)'(s) = -Gamma'(s)/Gamma(s)^(2 : ℕ)`.
The product-form basis of the reciprocal's Bell structure: iterating this (with `1/Gamma` entire) gives
`(1/Gamma)^(n) = (1/Gamma) * B_n(-psi-jet)` -- the Bell chain of `Gamma` with `psi -> -psi`
(`oneDivGamma_logDeriv_eq_neg_digamma`).  So the entire function `1/Gamma` inherits the full log-derivative
jet structure of `Gamma`, sign-flipped, and any hypertranscendence of `Gamma` transfers to it. -/
theorem oneDivGamma_deriv_eq (s : ℂ) (hs : ∀ p : ℕ, s ≠ -(p:ℂ)) :
    deriv (fun z => (Complex.Gamma z)⁻¹) s = -deriv Complex.Gamma s / (Complex.Gamma s)^(2 : ℕ) := by
  have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hd : DifferentiableAt ℂ Complex.Gamma s := (analyticAt_Gamma s hs).differentiableAt
  have h : HasDerivAt (fun z => (Complex.Gamma z)⁻¹)
      (-deriv Complex.Gamma s / (Complex.Gamma s)^(2 : ℕ)) s := hd.hasDerivAt.inv hne
  exact h.deriv

end GaloisForLFunctions
