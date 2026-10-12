import GaloisForLFunctions.RHTower.CosineProducerMeasurePortObstruction

/-!
# No compactly carried analytic port from the cosine producer to Ξ

Let `A_h = cos(hD)Ξ` (`LocalPort.cosineProducer`). For a radius `ρ`, let `L_{m,k}` be continuous
linear functionals on `C(D̄_ρ)`, i.e. complex Radon measures on the closed disc of radius `ρ`.

**Theorem** (`not_exists_analytic_port_cosineProducer`). For `h ≠ 0`,
`Σ_{m<M} t^m Σ_{k<K} L_{m,k}(w ↦ A_h^{(k)}(t + w)) = Ξ(t)` fails for some real `t`.

The statement covers, with polynomial weights in `t`:
- differential operators (`L` evaluation at `0`);
- finite combinations of complex translates (point masses);
- averages over compact planar sets, together with derivatives.

**Proof.**
* Separation (`eq_zero_of_ker_eq_zero`). If `Σ_{j<J} Φ^{(j)}(u) G_j(u) = 0` on `ℝ`, with every
  `G_j` entire of exponential type, then every `G_j` vanishes. The proof has three steps:
  - the cusp modes separate as `u → ∞`, because an exponential-type function decaying faster than
    every exponential on a ray vanishes (`IsExpType.eq_zero_of_superexp`);
  - each mode is a polynomial in `n²`;
  - the system is triangular, by the top cusp coefficient of `Φ^{(j)}`.
* Kernel (`apply_paperFT_shift`). `L(w ↦ (FΨ)(t + w)) = F(Ψ ĝ_L)(t)` with
  `ĝ_L(z) = L(w ↦ e^{izw})` of exponential type `|ρ|`. So the `m`-th symbol is
  `N_m(z) = cosh(hz) Σ_k (iz)^k ĝ_{L_{m,k}}(z)`.
* Leibniz form (`idIter_apply`). `t^m` acts as `(i d/du)^m`, whose `Φ^{(j)}`-coefficient is
  `i^m C(m,j) N_m^{(m-j)}`. By Cauchy's estimate, derivatives keep exponential type.
* Descent. Separation forces `N_m ≡ 0` for `m ≥ 1` and `N_0 ≡ 1`. But `N_0` vanishes at
  `z = iπ/(2h)`, a zero of `cosh(hz)`.
-/

open Complex MeasureTheory Filter Topology Set Polynomial Metric
open scoped Real

noncomputable section

namespace RHTower.AnalyticPort

open MeasurePort (cp linear_sub_exp_two_mul_le)

/-! ## Entire functions of exponential type -/

/-- Entire functions of exponential type. -/
def IsExpType (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ A τ : ℝ, 0 ≤ A ∧ 0 ≤ τ ∧ ∀ z, ‖f z‖ ≤ A * Real.exp (τ * ‖z‖)

theorem IsExpType.const (c : ℂ) : IsExpType fun _ => c :=
  ⟨differentiable_const c, ‖c‖, 0, norm_nonneg _, le_rfl, fun z => by simp⟩

theorem IsExpType.add {f g : ℂ → ℂ} (hf : IsExpType f) (hg : IsExpType g) :
    IsExpType fun z => f z + g z := by
  obtain ⟨hfd, A, τ, hA, hτ, hfb⟩ := hf
  obtain ⟨hgd, B, σ, hB, hσ, hgb⟩ := hg
  refine ⟨hfd.add hgd, A + B, max τ σ, by positivity, le_max_of_le_left hτ, fun z => ?_⟩
  have h1 : Real.exp (τ * ‖z‖) ≤ Real.exp (max τ σ * ‖z‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h2 : Real.exp (σ * ‖z‖) ≤ Real.exp (max τ σ * ‖z‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ A * Real.exp (τ * ‖z‖) + B * Real.exp (σ * ‖z‖) := add_le_add (hfb z) (hgb z)
    _ ≤ (A + B) * Real.exp (max τ σ * ‖z‖) := by nlinarith

theorem IsExpType.mul {f g : ℂ → ℂ} (hf : IsExpType f) (hg : IsExpType g) :
    IsExpType fun z => f z * g z := by
  obtain ⟨hfd, A, τ, hA, hτ, hfb⟩ := hf
  obtain ⟨hgd, B, σ, hB, hσ, hgb⟩ := hg
  refine ⟨hfd.mul hgd, A * B, τ + σ, by positivity, by positivity, fun z => ?_⟩
  rw [norm_mul]
  calc ‖f z‖ * ‖g z‖ ≤ (A * Real.exp (τ * ‖z‖)) * (B * Real.exp (σ * ‖z‖)) :=
        mul_le_mul (hfb z) (hgb z) (norm_nonneg _) (by positivity)
    _ = A * B * Real.exp ((τ + σ) * ‖z‖) := by rw [add_mul, Real.exp_add]; ring

theorem IsExpType.const_mul {f : ℂ → ℂ} (hf : IsExpType f) (c : ℂ) :
    IsExpType fun z => c * f z := (IsExpType.const c).mul hf

theorem IsExpType.sum_range (n : ℕ) {f : ℕ → ℂ → ℂ} (h : ∀ i < n, IsExpType (f i)) :
    IsExpType fun z => ∑ i ∈ Finset.range n, f i z := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero]
    exact IsExpType.const 0
  | succ n ih =>
    have e : (fun z => ∑ i ∈ Finset.range (n + 1), f i z) =
        fun z => (∑ i ∈ Finset.range n, f i z) + f n z :=
      funext fun z => Finset.sum_range_succ _ _
    rw [e]
    exact (ih fun i hi => h i (by omega)).add (h n (by omega))

theorem IsExpType.ite (p : Prop) [Decidable p] {f : ℂ → ℂ} (hf : IsExpType f) :
    IsExpType fun z => if p then f z else 0 := by
  by_cases hp : p
  · simp only [if_pos hp]; exact hf
  · simp only [if_neg hp]; exact IsExpType.const 0

theorem isExpType_cexp (c : ℂ) : IsExpType fun z => cexp (c * z) := by
  refine ⟨((differentiable_const c).mul differentiable_fun_id).cexp, 1, ‖c‖, zero_le_one,
    norm_nonneg _, fun z => ?_⟩
  rw [Complex.norm_exp, one_mul]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
  rw [norm_mul]

theorem isExpType_id : IsExpType fun z => z := by
  refine ⟨differentiable_fun_id, 1, 1, zero_le_one, zero_le_one, fun z => ?_⟩
  rw [one_mul, one_mul]
  linarith [Real.add_one_le_exp ‖z‖]

theorem isExpType_pow (k : ℕ) (c : ℂ) : IsExpType fun z => (c * z) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    exact IsExpType.const 1
  | succ k ih =>
    have e : (fun z => (c * z) ^ (k + 1)) = fun z => (c * z) ^ k * (c * z) :=
      funext fun z => pow_succ _ _
    rw [e]
    exact ih.mul (isExpType_id.const_mul c)

theorem isExpType_cosh (h : ℝ) : IsExpType fun z => Complex.cosh (h * z) := by
  have hs := ((isExpType_cexp (h : ℂ)).add (isExpType_cexp (-(h : ℂ)))).const_mul (1 / 2)
  have e : (fun z => Complex.cosh (h * z)) =
      fun z => 1 / 2 * (cexp (h * z) + cexp (-(h : ℂ) * z)) := by
    funext z; rw [Complex.cosh]; ring_nf
  rw [e]
  exact hs

/-- Cauchy's estimate: the derivative of a function of exponential type has exponential type. -/
theorem isExpType_deriv {f : ℂ → ℂ} (hf : IsExpType f) : IsExpType (deriv f) := by
  obtain ⟨hfd, A, τ, hA, hτ, hfb⟩ := hf
  have hdd : Differentiable ℂ (deriv f) := fun z => (hfd.analyticAt z).deriv.differentiableAt
  refine ⟨hdd, A * Real.exp τ, τ, by positivity, hτ, fun z => ?_⟩
  have hC : ∀ w ∈ sphere z 1, ‖f w‖ ≤ A * Real.exp τ * Real.exp (τ * ‖z‖) := by
    intro w hw
    have hwn : ‖w‖ ≤ ‖z‖ + 1 := by
      have := norm_le_norm_add_norm_sub' w z
      rw [mem_sphere, dist_eq_norm] at hw
      linarith
    calc ‖f w‖ ≤ A * Real.exp (τ * ‖w‖) := hfb w
      _ ≤ A * Real.exp (τ * (‖z‖ + 1)) := by gcongr
      _ = A * Real.exp τ * Real.exp (τ * ‖z‖) := by rw [mul_add, mul_one, Real.exp_add]; ring
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hfd.diffContOnCl hC
  simpa using this

theorem IsExpType.iterate_deriv {f : ℂ → ℂ} (hf : IsExpType f) (r : ℕ) :
    IsExpType (deriv^[r] f) := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [Function.iterate_succ_apply']; exact isExpType_deriv ih

theorem iterate_deriv_zero (r : ℕ) : deriv^[r] (0 : ℂ → ℂ) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih]
    funext z
    exact deriv_const z (0 : ℂ)

/-- **Uniqueness.** An entire function of exponential type decaying faster than every exponential
along the positive real axis vanishes. -/
theorem IsExpType.eq_zero_of_superexp {f : ℂ → ℂ} (hf : IsExpType f)
    (hdecay : ∀ M : ℝ, ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C * Real.exp (-(M * x))) : f = 0 := by
  obtain ⟨hfd, A, τ, hA, hτ, hfb⟩ := hf
  set b := τ + 1 with hb
  obtain ⟨C, hC⟩ := hdecay (b + 1)
  set g : ℂ → ℂ := fun z => f z * cexp (b * z) with hg
  have hgd : Differentiable ℂ g := hfd.mul ((differentiable_const _).mul differentiable_id).cexp
  have hgrow : ∀ z : ℂ, ‖g z‖ ≤ A * Real.exp ((τ + |b|) * ‖z‖) := by
    intro z
    rw [norm_mul, Complex.norm_exp]
    have he : (↑b * z).re ≤ |b| * ‖z‖ := by
      have := Complex.re_le_norm (↑b * z)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    calc ‖f z‖ * Real.exp (↑b * z).re ≤ A * Real.exp (τ * ‖z‖) * Real.exp (|b| * ‖z‖) := by
          gcongr; exact hfb z
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hC0 : 0 ≤ C := by
    have := hC 0 le_rfl
    simp at this
    exact (norm_nonneg _).trans this
  have hplus : ∀ x : ℝ, 0 ≤ x → ‖g x‖ ≤ (C + A) * Real.exp (-(1 * x)) := by
    intro x hx
    rw [norm_mul, show (b : ℂ) * x = ((b * x : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    calc ‖f x‖ * Real.exp (b * x) ≤ C * Real.exp (-((b + 1) * x)) * Real.exp (b * x) := by
          gcongr; exact hC x hx
      _ = C * Real.exp (-(1 * x)) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ (C + A) * Real.exp (-(1 * x)) := by gcongr; linarith
  have hminus : ∀ x : ℝ, x ≤ 0 → ‖g x‖ ≤ (C + A) * Real.exp (1 * x) := by
    intro x hx
    rw [norm_mul, show (b : ℂ) * x = ((b * x : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    have hfx := hfb x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hx] at hfx
    calc ‖f x‖ * Real.exp (b * x) ≤ A * Real.exp (τ * -x) * Real.exp (b * x) := by gcongr
      _ = A * Real.exp (1 * x) := by rw [mul_assoc, ← Real.exp_add, hb]; ring_nf
      _ ≤ (C + A) * Real.exp (1 * x) := by gcongr; linarith
  have hzero := eq_zero_of_two_ray_exponential_decay hgd hA (by positivity) one_pos hgrow hplus
    hminus
  funext z
  have := congrFun hzero z
  simp only [hg, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
  exact this

/-! ## Separation: `Φ^{(j)}` are independent over functions of exponential type -/

/-- The kernel `Σ_{j<J} Φ^{(j)}(u) G_j(u)`. -/
def ker (J : ℕ) (G : ℕ → ℂ → ℂ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range J, riemannKernelDeriv j u * G j u

theorem superExpDecay_term {g : ℂ → ℂ} (hg : IsExpType g) (j : ℕ) :
    SuperExpDecay fun u : ℝ => riemannKernelDeriv j u * g u := by
  obtain ⟨hgd, A, τ, hA, hτ, hb⟩ := hg
  have hcont : Continuous fun u : ℝ => riemannKernelDeriv j u * g u :=
    (continuous_riemannKernelDeriv j).mul (hgd.continuous.comp Complex.continuous_ofReal)
  refine ⟨hcont, fun c => ?_⟩
  have hD := ((superExpDecay_riemannKernelDeriv j).2 (c + τ)).const_mul A
  refine hD.mono' (hcont.norm.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hx := hb x
  rw [Complex.norm_real, Real.norm_eq_abs] at hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
  calc ‖riemannKernelDeriv j x‖ * ‖g x‖ * Real.exp (c * |x|)
      ≤ ‖riemannKernelDeriv j x‖ * (A * Real.exp (τ * |x|)) * Real.exp (c * |x|) := by gcongr
    _ = A * (‖riemannKernelDeriv j x‖ * Real.exp ((c + τ) * |x|)) := by
        rw [add_mul, Real.exp_add]; ring

theorem superExpDecay_ker {J : ℕ} {G : ℕ → ℂ → ℂ} (hG : ∀ j < J, IsExpType (G j)) :
    SuperExpDecay (ker J G) := by
  induction J with
  | zero =>
    have e : ker 0 G = 0 := by funext u; simp [ker]
    rw [e]
    exact ⟨continuous_const, fun c => by simp⟩
  | succ J ih =>
    have e : ker (J + 1) G = ker J G + fun u : ℝ => riemannKernelDeriv J u * G J u := by
      funext u; simp [ker, Finset.sum_range_succ]
    rw [e]
    exact (ih fun j hj => hG j (by omega)).add (superExpDecay_term (hG J (by omega)) J)

theorem cuspTerm_mul {D j : ℕ} (hD : (cp j).natDegree < D) (n : ℕ) (g : ℂ) (u : ℝ) :
    (cuspTerm (cp j) n u : ℂ) * g =
      (Real.exp (-π * ((n : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
        ∑ i ∈ Finset.range D, ((cp j).coeff i : ℂ) * ((n : ℂ) ^ 2) ^ i *
          cexp ((1 / 2 + 2 * i : ℂ) * u) * g := by
  unfold cuspTerm
  rw [eval_eq_sum_range' hD]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ((n : ℂ) ^ 2 * cexp (2 * (u : ℂ))) ^ i = ((n : ℂ) ^ 2) ^ i * cexp (2 * i * u) := by
    rw [mul_pow, ← Complex.exp_nat_mul]; ring_nf
  have e2 : cexp ((u : ℂ) / 2) * cexp (2 * i * u) = cexp ((1 / 2 + 2 * i : ℂ) * u) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e1, ← e2]; ring

/-- The `n`-th cusp head of a kernel. -/
def headF (J D : ℕ) (G : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range D,
    ((cp j).coeff i : ℂ) * ((n : ℂ) ^ 2) ^ i * cexp ((1 / 2 + 2 * i : ℂ) * z) * G j z

theorem isExpType_headF {J D : ℕ} {G : ℕ → ℂ → ℂ} (hG : ∀ j < J, IsExpType (G j)) (n : ℕ) :
    IsExpType (headF J D G n) := by
  unfold headF
  refine IsExpType.sum_range J fun j hj => IsExpType.sum_range D fun i _ => ?_
  exact ((isExpType_cexp _).const_mul _).mul (hG j hj)

/-- **Mode decomposition.** -/
theorem exists_modes_tail_le {D : ℕ} {G : ℕ → ℂ → ℂ} (N : ℕ) : ∀ J : ℕ,
    (∀ j < J, IsExpType (G j)) → (∀ j < J, (cp j).natDegree < D) →
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      ‖ker J G u - ∑ k ∈ Finset.range N,
          (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) : ℂ) *
            headF J D G (k + 1) u‖ ≤
        K * Real.exp (C * u) * Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u)) := by
  intro J
  induction J with
  | zero =>
    intro _ _
    refine ⟨0, 0, le_rfl, le_rfl, fun u _ => ?_⟩
    simp [ker, headF]
  | succ J ih =>
    intro hG hD
    obtain ⟨K₁, C₁, hK₁, hC₁, h₁⟩ :=
      ih (fun j hj => hG j (by omega)) (fun j hj => hD j (by omega))
    obtain ⟨B, hB, hBle⟩ := LocalPort.exists_abs_cuspSeries_tail_from_le (cp J) (N + 1) (by omega)
    obtain ⟨-, A, τ, hA, hτ, hall⟩ := hG J (by omega)
    set C₀ : ℝ := τ + (1 / 2 + 2 * (cp J).natDegree) with hC₀
    have hC₀0 : 0 ≤ C₀ := by positivity
    refine ⟨A * B + K₁, max C₀ C₁, by positivity, le_max_of_le_right hC₁, fun u hu => ?_⟩
    set Y := Real.exp (2 * u) with hY
    have hsplitR : cuspSeries (cp J) u = ∑ k ∈ Finset.range N, cuspTerm (cp J) (k + 1) u +
        ∑' n : ℕ, cuspTerm (cp J) (n + (N + 1)) u := by
      unfold cuspSeries
      rw [← (summable_cuspTerm (cp J) u).sum_add_tsum_nat_add N]
      rfl
    have hterm : ‖riemannKernelDeriv J u * G J u - ∑ k ∈ Finset.range N,
          (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
            ∑ i ∈ Finset.range D, ((cp J).coeff i : ℂ) * (((k + 1 : ℕ) : ℂ) ^ 2) ^ i *
              cexp ((1 / 2 + 2 * i : ℂ) * u) * G J u‖ ≤
        A * B * Real.exp (C₀ * u) * Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := by
      have hsplit : riemannKernelDeriv J u * G J u =
          ∑ k ∈ Finset.range N, (cuspTerm (cp J) (k + 1) u : ℂ) * G J u +
            ((∑' n : ℕ, cuspTerm (cp J) (n + (N + 1)) u : ℝ) : ℂ) * G J u := by
        unfold riemannKernelDeriv
        rw [show cuspDeriv^[J] riemannCuspPoly = cp J from rfl, hsplitR]
        push_cast
        rw [add_mul, Finset.sum_mul]
      rw [hsplit, Finset.sum_congr rfl fun k _ => cuspTerm_mul (hD J (by omega)) (k + 1) (G J u) u,
        add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hx := hall u
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] at hx
      have ht := hBle u hu
      calc |∑' n : ℕ, cuspTerm (cp J) (n + (N + 1)) u| * ‖G J u‖
          ≤ (B * Real.exp ((1 / 2 + 2 * (cp J).natDegree) * u) *
              Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y)) * (A * Real.exp (τ * u)) := by
            gcongr
        _ = A * B * Real.exp (C₀ * u) * Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := by
            rw [hC₀, show (τ + (1 / 2 + 2 * ((cp J).natDegree : ℝ))) * u =
              (1 / 2 + 2 * ((cp J).natDegree : ℝ)) * u + τ * u by ring, Real.exp_add]
            ring
    have hrest := h₁ u hu
    have hE0 : 0 ≤ Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := (Real.exp_pos _).le
    have hm1 : Real.exp (C₀ * u) ≤ Real.exp (max C₀ C₁ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
    have hm2 : Real.exp (C₁ * u) ≤ Real.exp (max C₀ C₁ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu)
    have hker : ker (J + 1) G u = ker J G u + riemannKernelDeriv J u * G J u := by
      simp only [ker, Finset.sum_range_succ]
    have hsum_split : ∑ k ∈ Finset.range N,
        (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) * headF (J + 1) D G (k + 1) u =
        ∑ k ∈ Finset.range N, (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
            headF J D G (k + 1) u +
        ∑ k ∈ Finset.range N, (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
          ∑ i ∈ Finset.range D, ((cp J).coeff i : ℂ) * (((k + 1 : ℕ) : ℂ) ^ 2) ^ i *
            cexp ((1 / 2 + 2 * i : ℂ) * u) * G J u := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [headF, Finset.sum_range_succ]
      ring
    rw [hker, hsum_split]
    calc _ = ‖(riemannKernelDeriv J u * G J u - ∑ k ∈ Finset.range N,
            (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) *
              ∑ i ∈ Finset.range D, ((cp J).coeff i : ℂ) * (((k + 1 : ℕ) : ℂ) ^ 2) ^ i *
                cexp ((1 / 2 + 2 * i : ℂ) * u) * G J u) +
          (ker J G u - ∑ k ∈ Finset.range N,
            (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Y)) : ℂ) * headF J D G (k + 1) u)‖ := by
          congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hterm hrest)
      _ ≤ (A * B + K₁) * Real.exp (max C₀ C₁ * u) *
            Real.exp (-(π * ((N + 1 : ℕ) : ℝ) ^ 2) * Y) := by
          have := mul_le_mul_of_nonneg_right hm1 (mul_nonneg (mul_nonneg hA hB) hE0)
          have := mul_le_mul_of_nonneg_right hm2 (mul_nonneg hK₁ hE0)
          nlinarith

/-- **Mode separation.** A vanishing kernel has vanishing cusp heads. -/
theorem headF_eq_zero {J D : ℕ} {G : ℕ → ℂ → ℂ} (hG : ∀ j < J, IsExpType (G j))
    (hD : ∀ j < J, (cp j).natDegree < D) (h0 : ∀ u : ℝ, ker J G u = 0) (n : ℕ) :
    headF J D G (n + 1) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨K, C, hK, hC, htail⟩ := exists_modes_tail_le (n + 1) J hG hD
    refine (isExpType_headF hG (n + 1)).eq_zero_of_superexp fun M => ?_
    set a : ℝ := π * (2 * n + 3) with ha
    have ha0 : 0 < a := by positivity
    refine ⟨K * Real.exp ((C + M) ^ 2 / (8 * a)), fun x hx => ?_⟩
    have h := htail x hx
    have hprev : ∑ k ∈ Finset.range n,
        (Real.exp (-π * (((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))) : ℂ) *
          headF J D G (k + 1) x = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [ih k (Finset.mem_range.mp hk)]; simp
    rw [h0 x, Finset.sum_range_succ, hprev, zero_add, zero_sub, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    set Y := Real.exp (2 * x) with hY
    have hsplit : Real.exp (-(π * ((n + 1 + 1 : ℕ) : ℝ) ^ 2) * Y) =
        Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) * Real.exp (-a * Y) := by
      rw [← Real.exp_add]; congr 1; rw [ha]; push_cast; ring
    rw [hsplit] at h
    have hE := Real.exp_pos (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y))
    have h2 : Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) * ‖headF J D G (n + 1) x‖ ≤
        Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          (K * Real.exp (C * x) * Real.exp (-a * Y)) := by
      have e : K * Real.exp (C * x) * (Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          Real.exp (-a * Y)) = Real.exp (-π * (((n + 1 : ℕ) : ℝ) ^ 2 * Y)) *
          (K * Real.exp (C * x) * Real.exp (-a * Y)) := by ring
      linarith [h, e]
    have h' := le_of_mul_le_mul_left h2 hE
    have hq := linear_sub_exp_two_mul_le (b := C + M) ha0 hx
    calc ‖headF J D G (n + 1) x‖ ≤ K * Real.exp (C * x) * Real.exp (-a * Y) := h'
      _ = K * Real.exp ((C + M) * x - a * Y) * Real.exp (-(M * x)) := by
          rw [mul_assoc K, mul_assoc K, ← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ K * Real.exp ((C + M) ^ 2 / (8 * a)) * Real.exp (-(M * x)) := by
          gcongr

/-- The coefficient functions `W_i = Σ_j coeff_i(cp j) · G_j`. -/
def coeffW (J : ℕ) (G : ℕ → ℂ → ℂ) (i : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range J, ((cp j).coeff i : ℂ) * G j z

theorem headF_eq_sum (J D : ℕ) (G : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) :
    headF J D G n z = ∑ i ∈ Finset.range D,
      ((n : ℂ) ^ 2) ^ i * (cexp ((1 / 2 + 2 * i : ℂ) * z) * coeffW J G i z) := by
  unfold headF coeffW
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Coefficient vanishing.** -/
theorem coeffW_eq_zero {J D : ℕ} {G : ℕ → ℂ → ℂ} (hG : ∀ j < J, IsExpType (G j))
    (hD : ∀ j < J, (cp j).natDegree < D) (h0 : ∀ u : ℝ, ker J G u = 0) {i : ℕ} (hi : i < D)
    (z : ℂ) : coeffW J G i z = 0 := by
  set Pz : ℂ[X] := ∑ k ∈ Finset.range D,
    C (cexp ((1 / 2 + 2 * k : ℂ) * z) * coeffW J G k z) * X ^ k with hPz
  have hroot : ∀ n : ℕ, Pz.IsRoot (((n + 1 : ℕ) : ℂ) ^ 2) := by
    intro n
    have h0 := congrFun (headF_eq_zero hG hD h0 n) z
    rw [Pi.zero_apply, headF_eq_sum] at h0
    rw [Polynomial.IsRoot.def, hPz, Polynomial.eval_finsetSum]
    simpa [mul_comm] using h0
  have hPz0 : Pz = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Pz ?_
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ 2))
      ?_ hroot
    intro a b hab
    simp only at hab
    have h1 : (a + 1) ^ 2 = (b + 1) ^ 2 := by exact_mod_cast hab
    have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) h1
    omega
  have hcoeff := congrArg (fun q : ℂ[X] => q.coeff i) hPz0
  simp only [hPz, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero, Finset.sum_ite_eq, Finset.mem_range, hi, if_true] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (Complex.exp_ne_zero _)

/-- **Separation.** If `Σ_{j<J} Φ^{(j)} G_j` vanishes on the real line and every `G_j` is entire
of exponential type, then every `G_j` vanishes. -/
theorem eq_zero_of_ker_eq_zero {J : ℕ} {G : ℕ → ℂ → ℂ} (hG : ∀ j < J, IsExpType (G j))
    (h0 : ∀ u : ℝ, ker J G u = 0) : ∀ j < J, G j = 0 := by
  have hD : ∀ j < J, (cp j).natDegree < J + 3 := fun j hj => by
    have : (cp j).natDegree ≤ j + 2 := natDegree_riemannKernelPoly_le j
    omega
  have key : ∀ k j, J - k ≤ j → j < J → G j = 0 := by
    intro k
    induction k with
    | zero => intro j hj hjJ; omega
    | succ k ih =>
      intro j hj hjJ
      by_cases hj' : J - k ≤ j
      · exact ih j hj' hjJ
      · funext z
        have hW := coeffW_eq_zero hG hD h0 (i := j + 2) (by omega) z
        unfold coeffW at hW
        rw [Finset.sum_eq_single j] at hW
        · have hc : ((cp j).coeff (j + 2) : ℂ) ≠ 0 := by
            rw [Ne, Complex.ofReal_eq_zero]; exact LocalPort.cuspPoly_coeff_top_ne_zero j
          exact (mul_eq_zero.mp hW).resolve_left hc
        · intro j' hj'J hj'j
          rcases lt_or_gt_of_ne hj'j with hlt | hgt
          · have hdeg : (cp j').natDegree ≤ j' + 2 := natDegree_riemannKernelPoly_le j'
            have : (cp j').coeff (j + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
            simp [this]
          · rw [ih j' (by omega) (Finset.mem_range.mp hj'J)]; simp
        · intro h; exact absurd (Finset.mem_range.mpr hjJ) h
  intro j hj
  exact key J j (by omega) hj

/-! ## `i d/du` on coefficient families -/

/-- `i d/du` on kernels: `Φ^{(j)} G_j ↦ i (Φ^{(j+1)} G_j + Φ^{(j)} G_j')`, regrouped by `j`. -/
def idfam (J : ℕ) (G : ℕ → ℂ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  I * ((if j < J then deriv (G j) z else 0) + (if j = 0 then 0 else G (j - 1) z))

theorem isExpType_idfam {J : ℕ} {G : ℕ → ℂ → ℂ} (hG : ∀ j < J, IsExpType (G j)) :
    ∀ j < J + 1, IsExpType (idfam J G j) := by
  intro j hj
  unfold idfam
  refine IsExpType.const_mul (IsExpType.add ?_ ?_) I
  · by_cases h : j < J
    · simp only [if_pos h]; exact isExpType_deriv (hG j h)
    · simp only [if_neg h]; exact IsExpType.const 0
  · by_cases h : j = 0
    · simp only [if_pos h]; exact IsExpType.const 0
    · simp only [if_neg h]; exact hG (j - 1) (by omega)

theorem hasDerivAt_ker {J : ℕ} {G : ℕ → ℂ → ℂ} (hG : ∀ j < J, IsExpType (G j)) (u : ℝ) :
    HasDerivAt (ker J G) (-I * ker (J + 1) (idfam J G) u) u := by
  have hsum : HasDerivAt (fun x : ℝ => ∑ j ∈ Finset.range J, riemannKernelDeriv j x * G j x)
      (∑ j ∈ Finset.range J, (riemannKernelDeriv (j + 1) u * G j u +
        riemannKernelDeriv j u * deriv (G j) u)) u := by
    refine HasDerivAt.fun_sum fun j hj => ?_
    have hGd : HasDerivAt (fun x : ℝ => G j x) (deriv (G j) u) u :=
      ((hG j (Finset.mem_range.mp hj)).1 u).hasDerivAt.comp_ofReal
    exact (hasDerivAt_riemannKernelDeriv j u).mul hGd
  refine hsum.congr_deriv ?_
  have ha : ∑ j ∈ Finset.range (J + 1),
      riemannKernelDeriv j u * (if j < J then deriv (G j) u else 0) =
      ∑ j ∈ Finset.range J, riemannKernelDeriv j u * deriv (G j) u := by
    rw [Finset.sum_range_succ, if_neg (lt_irrefl J), mul_zero, add_zero]
    exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
  have hb : ∑ j ∈ Finset.range (J + 1),
      riemannKernelDeriv j u * (if j = 0 then 0 else G (j - 1) u) =
      ∑ j ∈ Finset.range J, riemannKernelDeriv (j + 1) u * G j u := by
    rw [Finset.sum_range_succ']
    simp
  have e : ker (J + 1) (idfam J G) u = I * ∑ j ∈ Finset.range J,
      (riemannKernelDeriv (j + 1) u * G j u + riemannKernelDeriv j u * deriv (G j) u) := by
    calc ker (J + 1) (idfam J G) u = I * (∑ j ∈ Finset.range (J + 1),
          riemannKernelDeriv j u * (if j < J then deriv (G j) u else 0) +
          ∑ j ∈ Finset.range (J + 1),
          riemannKernelDeriv j u * (if j = 0 then 0 else G (j - 1) u)) := by
          unfold ker idfam
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = _ := by
          rw [ha, hb, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [e, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]

open Zeta23 in
/-- Multiplication by `z` on the transform is `i d/du` on the kernel. -/
theorem mul_paperFT_ker {J : ℕ} {G : ℕ → ℂ → ℂ} (hG : ∀ j < J, IsExpType (G j)) (z : ℂ) :
    z * paperFT (ker J G) z = paperFT (ker (J + 1) (idfam J G)) z := by
  have hdec := superExpDecay_ker hG
  have hdec' := superExpDecay_ker (isExpType_idfam hG)
  have hdd : SuperExpDecay fun u => -I * ker (J + 1) (idfam J G) u := by
    refine ⟨continuous_const.mul hdec'.1, fun c => ?_⟩
    have e : (fun u : ℝ => ‖-I * ker (J + 1) (idfam J G) u‖ * Real.exp (c * |u|)) =
        fun u => ‖ker (J + 1) (idfam J G) u‖ * Real.exp (c * |u|) := by
      funext u; rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    rw [e]; exact hdec'.2 c
  have h := paperFT_deriv_of_superExpDecay hdec hdd (hasDerivAt_ker hG) z
  have hlin : paperFT (fun u => -I * ker (J + 1) (idfam J G) u) z =
      -I * paperFT (ker (J + 1) (idfam J G)) z := by
    unfold paperFT; rw [← integral_const_mul]; congr 1; funext u; ring
  rw [hlin] at h
  have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr I_ne_zero
  refine (mul_left_cancel₀ hI ?_).symm
  rw [h]; ring

/-- The coefficient families of `(i d/du)^m [Φ N]`. -/
def idIter (N : ℂ → ℂ) : ℕ → ℕ → ℂ → ℂ
  | 0 => fun j => if j = 0 then N else 0
  | m + 1 => idfam (m + 1) (idIter N m)

/-- **Leibniz form.** The `Φ^{(j)}`-coefficient of `(i d/du)^m [Φ N]` is
`i^m C(m,j) N^{(m-j)}`. -/
theorem idIter_apply {N : ℂ → ℂ} (hN : IsExpType N) (m : ℕ) : ∀ j z,
    idIter N m j z = if j ≤ m then I ^ m * (m.choose j : ℂ) * deriv^[m - j] N z else 0 := by
  have hd : ∀ r, Differentiable ℂ (deriv^[r] N) := fun r => (hN.iterate_deriv r).1
  induction m with
  | zero =>
    intro j z
    rcases j with _ | j
    · simp [idIter]
    · simp [idIter]
  | succ m ih =>
    intro j z
    show I * ((if j < m + 1 then deriv (idIter N m j) z else 0) +
      (if j = 0 then 0 else idIter N m (j - 1) z)) = _
    rcases j with _ | j
    · have e : idIter N m 0 = fun z => I ^ m * deriv^[m] N z := by
        funext w; rw [ih 0 w]; simp
      rw [if_pos (Nat.succ_pos m), e, deriv_const_mul _ ((hd m) z), if_pos rfl,
        if_pos (Nat.zero_le _)]
      simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, add_zero,
        Function.iterate_succ_apply', pow_succ]
      ring
    · rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, ih j z]
      by_cases hjm : j + 1 ≤ m
      · have e : idIter N m (j + 1) =
            fun z => I ^ m * (m.choose (j + 1) : ℂ) * deriv^[m - (j + 1)] N z := by
          funext w; rw [ih (j + 1) w, if_pos hjm]
        rw [if_pos (by omega : j + 1 < m + 1), e, deriv_const_mul _ ((hd _) z),
          if_pos (by omega : j ≤ m), if_pos (by omega : j + 1 ≤ m + 1)]
        have h1 : m + 1 - (j + 1) = m - (j + 1) + 1 := by omega
        have h2 : m - j = m - (j + 1) + 1 := by omega
        rw [h1, h2, Function.iterate_succ_apply', Nat.choose_succ_succ' m j]
        push_cast
        ring
      · by_cases hjm' : j = m
        · subst hjm'
          rw [if_neg (lt_irrefl _), if_pos le_rfl, if_pos le_rfl]
          simp only [Nat.choose_self, Nat.sub_self, Function.iterate_zero, id, Nat.cast_one,
            mul_one, zero_add, pow_succ]
          ring
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp

theorem isExpType_idIter {N : ℂ → ℂ} (hN : IsExpType N) (m j : ℕ) :
    IsExpType (idIter N m j) := by
  have e : idIter N m j =
      fun z => if j ≤ m then I ^ m * (m.choose j : ℂ) * deriv^[m - j] N z else 0 :=
    funext (idIter_apply hN m j)
  rw [e]
  exact IsExpType.ite _ ((hN.iterate_deriv _).const_mul _)

theorem ker_one_idIter_zero (N : ℂ → ℂ) (u : ℝ) :
    ker 1 (idIter N 0) u = riemannPhiKernel u * N u := by
  simp [ker, idIter, riemannKernelDeriv_zero]

open Zeta23 in
theorem pow_mul_paperFT_idIter {N : ℂ → ℂ} (hN : IsExpType N) (m : ℕ) (z : ℂ) :
    z ^ m * paperFT (ker 1 (idIter N 0)) z = paperFT (ker (m + 1) (idIter N m)) z := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_comm (z ^ m) z, mul_assoc, ih,
      mul_paperFT_ker (fun j _ => isExpType_idIter hN m j)]
    rfl

/-! ## Analytic functionals carried by a closed disc -/

/-- The closed disc of radius `ρ`. -/
abbrev Disc (ρ : ℝ) : Type := closedBall (0 : ℂ) ρ

instance (ρ : ℝ) : CompactSpace (Disc ρ) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall 0 ρ)

/-- The coordinate `w ↦ -iw` on the disc. -/
def discCoord (ρ : ℝ) : C(Disc ρ, ℂ) := ⟨fun w => -I * (w : ℂ), by fun_prop⟩

/-- The Fourier–Borel transform `ĝ_L(z) = L(w ↦ e^{izw})`. -/
def ghat {ρ : ℝ} (L : C(Disc ρ, ℂ) →L[ℂ] ℂ) (z : ℂ) : ℂ :=
  compactFourierBorel L (discCoord ρ) z

theorem norm_disc_le {ρ : ℝ} (w : Disc ρ) : ‖(w : ℂ)‖ ≤ |ρ| := by
  have := w.2
  rw [mem_closedBall, dist_zero_right] at this
  exact this.trans (le_abs_self ρ)

theorem isExpType_ghat {ρ : ℝ} (L : C(Disc ρ, ℂ) →L[ℂ] ℂ) : IsExpType (ghat L) := by
  refine ⟨fun z => ((compactFourierBorel_analyticOnNhd L (discCoord ρ)) z
    (Set.mem_univ z)).differentiableAt, ‖L‖, |ρ|, norm_nonneg _, abs_nonneg _, fun z => ?_⟩
  have hre : ∀ w : Disc ρ, -|ρ| * ‖z‖ ≤ (z * discCoord ρ w).re := by
    intro w
    have h2 := Complex.abs_re_le_norm (z * discCoord ρ w)
    have h3 : ‖z * discCoord ρ w‖ = ‖z‖ * ‖(w : ℂ)‖ := by
      simp [discCoord]
    rw [h3] at h2
    have h4 : ‖z‖ * ‖(w : ℂ)‖ ≤ ‖z‖ * |ρ| :=
      mul_le_mul_of_nonneg_left (norm_disc_le w) (norm_nonneg z)
    linarith [neg_abs_le (z * discCoord ρ w).re]
  have h := norm_compactFourierBorel_le L (discCoord ρ) z (-|ρ|) hre
  rw [neg_neg] at h
  exact h

theorem norm_discExp_le {ρ : ℝ} (u : ℝ) :
    ‖compactExponentialTest (discCoord ρ) (u : ℂ)‖ ≤ Real.exp (|ρ| * |u|) := by
  refine (ContinuousMap.norm_le _ (Real.exp_nonneg _)).2 fun w => ?_
  rw [compactExponentialTest_apply, Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have h2 := Complex.re_le_norm (-(u : ℂ) * discCoord ρ w)
  have h3 : ‖-(u : ℂ) * discCoord ρ w‖ = |u| * ‖(w : ℂ)‖ := by
    simp [discCoord]
  rw [h3] at h2
  have h4 : |u| * ‖(w : ℂ)‖ ≤ |u| * |ρ| := mul_le_mul_of_nonneg_left (norm_disc_le w) (abs_nonneg u)
  linarith

open Zeta23 in
/-- **Interchange.** A functional on the disc applied to `w ↦ (FΨ)(t + w)` is the transform of
`Ψ · ĝ_L` at `t`. -/
theorem apply_paperFT_shift {ρ : ℝ} (L : C(Disc ρ, ℂ) →L[ℂ] ℂ) {κ : ℝ → ℂ}
    (hκ : SuperExpDecay κ) (t : ℝ) (f : C(Disc ρ, ℂ))
    (hf : ∀ w : Disc ρ, f w = paperFT κ ((t : ℂ) + w)) :
    L f = paperFT (fun u => κ u * ghat L u) t := by
  set g : ℝ → ℂ := fun u => κ u * cexp (I * t * u) with hg
  set E : ℝ → C(Disc ρ, ℂ) := fun u => compactExponentialTest (discCoord ρ) (u : ℂ) with hE
  have hEc : Continuous E :=
    (compactExponentialTest_analyticOnNhd (discCoord ρ)).continuous.comp Complex.continuous_ofReal
  have hgc : Continuous g := hκ.1.mul (by fun_prop)
  have hint : Integrable fun u => g u • E u := by
    refine (hκ.2 |ρ|).mono' (hgc.smul hEc).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [norm_smul]
    have hgu : ‖g u‖ = ‖κ u‖ := by
      rw [hg]
      simp only [norm_mul]
      rw [show I * (t : ℂ) * u = ((t * u : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    rw [hgu]
    exact mul_le_mul_of_nonneg_left (norm_discExp_le u) (norm_nonneg _)
  have hfun : f = ∫ u, g u • E u := by
    ext w
    have h1 := ContinuousLinearMap.integral_comp_comm (ContinuousMap.evalCLM ℂ w) hint
    rw [ContinuousMap.evalCLM_apply] at h1
    rw [← h1, hf w]
    simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul, hE,
      compactExponentialTest_apply, hg]
    unfold paperFT
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [discCoord, ContinuousMap.coe_mk]
    rw [show I * ((t : ℂ) + (w : ℂ)) * (u : ℂ) = I * t * u + -(u : ℂ) * (-I * (w : ℂ)) by ring,
      Complex.exp_add]
    ring
  rw [hfun, ← ContinuousLinearMap.integral_comp_comm L hint]
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [ContinuousLinearMap.map_smul, smul_eq_mul, hg, hE]
  have hfb : L (compactExponentialTest (discCoord ρ) (u : ℂ)) = ghat L u := rfl
  rw [hfb]
  ring

/-! ## Ports built from translates and derivatives of the cosine producer -/

/-- The function `w ↦ A_h^{(k)}(t + w)` on the disc. -/
def shiftDerivFun (h ρ : ℝ) (k : ℕ) (t : ℝ) : C(Disc ρ, ℂ) :=
  ⟨fun w => iteratedDeriv k (LocalPort.cosineProducer h) ((t : ℂ) + w), by
    have hd : Differentiable ℂ (iteratedDeriv k (LocalPort.cosineProducer h)) := by
      rw [LocalPort.cosineProducer_eq_paperFT, LocalPort.iteratedDeriv_paperFT_kfun]
      exact fun z => (LocalPort.hasDerivAt_paperFT_of_superExpDecay
        (LocalPort.KFun.superExpDecay _) z).differentiableAt
    exact hd.continuous.comp (continuous_const.add continuous_subtype_val)⟩

theorem eval_iterate_mulIU (h : ℝ) (k : ℕ) (u : ℝ) :
    LocalPort.KFun.eval (LocalPort.KFun.mulIU^[k] (LocalPort.cosineKernel h)) u =
      riemannPhiKernel u * ((I * u) ^ k * Complex.cosh (h * u)) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero, id, LocalPort.cosineKernel_eval, pow_zero, one_mul,
      Complex.ofReal_cosh]
    push_cast; ring
  | succ k ih =>
    rw [Function.iterate_succ_apply', LocalPort.KFun.eval_mulIU, ih]; ring

open Zeta23 in
theorem apply_shiftDerivFun {ρ : ℝ} (h : ℝ) (L : C(Disc ρ, ℂ) →L[ℂ] ℂ) (k : ℕ) (t : ℝ) :
    L (shiftDerivFun h ρ k t) = paperFT (ker 1 (idIter
      (fun z => (I * z) ^ k * Complex.cosh (h * z) * ghat L z) 0)) t := by
  have hκ := LocalPort.KFun.superExpDecay (LocalPort.KFun.mulIU^[k] (LocalPort.cosineKernel h))
  rw [apply_paperFT_shift L hκ t (shiftDerivFun h ρ k t) fun w => by
    simp only [shiftDerivFun, ContinuousMap.coe_mk]
    rw [LocalPort.cosineProducer_eq_paperFT, LocalPort.iteratedDeriv_paperFT_kfun]]
  unfold paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [ker_one_idIter_zero, eval_iterate_mulIU]
  ring

open Zeta23 in
theorem sum_paperFT_phi_mul {K : ℕ} {N : ℕ → ℂ → ℂ} (hN : ∀ k < K, IsExpType (N k)) (z : ℂ) :
    ∑ k ∈ Finset.range K, paperFT (ker 1 (idIter (N k) 0)) z =
      paperFT (ker 1 (idIter (fun w => ∑ k ∈ Finset.range K, N k w) 0)) z := by
  unfold paperFT
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ker_one_idIter_zero]
    rw [Finset.mul_sum, Finset.sum_mul]
  · intro k hk
    exact (superExpDecay_ker (J := 1) (G := idIter (N k) 0) fun j _ =>
      isExpType_idIter (hN k (Finset.mem_range.mp hk)) 0 j).integrable_mul_cexp z

/-- The symbol `cosh(hz) Σ_k (iz)^k ĝ_{L_k}(z)` of `Σ_k L_k(w ↦ A_h^{(k)}(t + w))`. -/
def portSymbol (h : ℝ) {ρ : ℝ} (K : ℕ) (L : ℕ → C(Disc ρ, ℂ) →L[ℂ] ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range K, (I * z) ^ k * Complex.cosh (h * z) * ghat (L k) z

theorem isExpType_portSymbol (h : ℝ) {ρ : ℝ} (K : ℕ) (L : ℕ → C(Disc ρ, ℂ) →L[ℂ] ℂ) :
    IsExpType (portSymbol h K L) :=
  IsExpType.sum_range K fun k _ =>
    ((isExpType_pow k I).mul (isExpType_cosh h)).mul (isExpType_ghat (L k))

open Zeta23 in
theorem sum_apply_shiftDerivFun (h : ℝ) {ρ : ℝ} (K : ℕ) (L : ℕ → C(Disc ρ, ℂ) →L[ℂ] ℂ)
    (t : ℝ) : ∑ k ∈ Finset.range K, L k (shiftDerivFun h ρ k t) =
      paperFT (ker 1 (idIter (portSymbol h K L) 0)) t := by
  rw [Finset.sum_congr rfl fun k _ => apply_shiftDerivFun h (L k) k t]
  exact sum_paperFT_phi_mul (fun k _ =>
    ((isExpType_pow k I).mul (isExpType_cosh h)).mul (isExpType_ghat (L k))) t

/-- The `Φ^{(j)}`-coefficient of `(i d/du)^m [Φ N_m]`, on the common index range. -/
def portFam (N : ℕ → ℂ → ℂ) (m j : ℕ) (z : ℂ) : ℂ :=
  if j ≤ m then I ^ m * (m.choose j : ℂ) * deriv^[m - j] (N m) z else 0

/-- The coefficients of `Σ_m (i d/du)^m [Φ N_m] - Φ`. -/
def portTotal (M : ℕ) (N : ℕ → ℂ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range M, portFam N m j z + (if j = 0 then -1 else 0)

theorem ker_add (J : ℕ) (F G : ℕ → ℂ → ℂ) (u : ℝ) :
    ker J (fun j z => F j z + G j z) u = ker J F u + ker J G u := by
  simp only [ker, mul_add, Finset.sum_add_distrib]

theorem ker_sum (J M : ℕ) (F : ℕ → ℕ → ℂ → ℂ) (u : ℝ) :
    ker J (fun j z => ∑ m ∈ Finset.range M, F m j z) u =
      ∑ m ∈ Finset.range M, ker J (F m) u := by
  simp only [ker, Finset.mul_sum]
  exact Finset.sum_comm

theorem ker_delta (J : ℕ) (c : ℂ) (u : ℝ) :
    ker (J + 1) (fun j _ => if j = 0 then c else 0) u = riemannPhiKernel u * c := by
  simp [ker, riemannKernelDeriv_zero]

theorem ker_idIter_eq_portFam {N : ℕ → ℂ → ℂ} (hN : ∀ m, IsExpType (N m)) {m M : ℕ}
    (hm : m < M) (u : ℝ) : ker (m + 1) (idIter (N m) m) u = ker (M + 1) (portFam N m) u := by
  unfold ker
  rw [← Finset.sum_range_add_sum_Ico _ (show m + 1 ≤ M + 1 by omega)]
  have hz : ∑ j ∈ Finset.Ico (m + 1) (M + 1), riemannKernelDeriv j u * portFam N m j u = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [Finset.mem_Ico] at hj
      rw [portFam, if_neg (by omega), mul_zero]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [idIter_apply (hN m), portFam]

open Zeta23 in
/-- **No compactly carried analytic port from the cosine producer to `Ξ`.** For real `h ≠ 0`,
any radius `ρ`, and continuous linear functionals `L_{m,k}` on `C(D̄_ρ)` (complex Radon measures on
the closed disc of radius `ρ`), `Σ_{m<M} t^m Σ_{k<K} L_{m,k}(w ↦ A_h^{(k)}(t + w)) = Ξ(t)` fails
for some real `t`. -/
theorem not_exists_analytic_port_cosineProducer {h : ℝ} (hh : h ≠ 0) (ρ : ℝ) (M K : ℕ)
    (L : ℕ → ℕ → C(Disc ρ, ℂ) →L[ℂ] ℂ) :
    ¬ ∀ t : ℝ, ∑ m ∈ Finset.range M, (t : ℂ) ^ m *
      ∑ k ∈ Finset.range K, L m k (shiftDerivFun h ρ k t) = XiC t := by
  intro H
  set N : ℕ → ℂ → ℂ := fun m => portSymbol h K (L m) with hNdef
  have hN : ∀ m, IsExpType (N m) := fun m => isExpType_portSymbol h K (L m)
  have hG : ∀ j < M + 1, IsExpType (portTotal M N j) := fun j _ =>
    (IsExpType.sum_range M fun m _ =>
      IsExpType.ite _ (((hN m).iterate_deriv _).const_mul _)).add
      (IsExpType.ite _ (IsExpType.const (-1)))
  have hPhi : ∀ w : ℂ, paperFT riemannPhiKernel w = XiC w := fun w => by
    rw [paperFT_riemannPhiKernel, riemannPhiTransform_eq_xi, XiC, mul_comm]
  have hm : ∀ m (t : ℝ), (t : ℂ) ^ m * ∑ k ∈ Finset.range K, L m k (shiftDerivFun h ρ k t) =
      paperFT (ker (m + 1) (idIter (N m) m)) t := by
    intro m t
    rw [sum_apply_shiftDerivFun h K (L m) t, pow_mul_paperFT_idIter (hN m)]
  have hkerT : ∀ u : ℝ, ker (M + 1) (portTotal M N) u =
      ∑ m ∈ Finset.range M, ker (m + 1) (idIter (N m) m) u - riemannPhiKernel u := by
    intro u
    have e1 : ker (M + 1) (portTotal M N) u =
        ker (M + 1) (fun j z => ∑ m ∈ Finset.range M, portFam N m j z) u +
          ker (M + 1) (fun j _ => if j = 0 then (-1 : ℂ) else 0) u :=
      ker_add _ _ _ u
    rw [e1, ker_sum, ker_delta,
      Finset.sum_congr rfl fun m hm => ker_idIter_eq_portFam hN (Finset.mem_range.mp hm) u]
    ring
  have htot : ∀ t : ℝ, paperFT (ker (M + 1) (portTotal M N)) t = 0 := by
    intro t
    have hint_m : ∀ m ∈ Finset.range M,
        Integrable fun u : ℝ => ker (m + 1) (idIter (N m) m) u * cexp (I * t * u) :=
      fun m _ => (superExpDecay_ker fun j _ => isExpType_idIter (hN m) m j).integrable_mul_cexp t
    have hintΦ : Integrable fun u : ℝ => riemannPhiKernel u * cexp (I * t * u) := by
      have := (superExpDecay_riemannKernelDeriv 0).integrable_mul_cexp (t : ℂ)
      rwa [riemannKernelDeriv_zero] at this
    calc paperFT (ker (M + 1) (portTotal M N)) t
        = ∑ m ∈ Finset.range M, paperFT (ker (m + 1) (idIter (N m) m)) t -
            paperFT riemannPhiKernel t := by
          unfold paperFT
          rw [← integral_finsetSum _ hint_m,
            ← integral_sub (integrable_finsetSum _ hint_m) hintΦ]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp only
          rw [hkerT u, sub_mul, Finset.sum_mul]
      _ = ∑ m ∈ Finset.range M, (t : ℂ) ^ m *
            ∑ k ∈ Finset.range K, L m k (shiftDerivFun h ρ k t) - XiC t := by
          rw [Finset.sum_congr rfl fun m _ => (hm m t).symm, hPhi]
      _ = 0 := by rw [H t, sub_self]
  have hK0 : ker (M + 1) (portTotal M N) = 0 :=
    LocalPort.eq_zero_of_paperFT_real_eq_zero (superExpDecay_ker hG) htot
  have hsep := eq_zero_of_ker_eq_zero hG fun u => by rw [hK0]; rfl
  -- descent through the derivative orders
  have key : ∀ k m, 1 ≤ m → m < M → M - k ≤ m → N m = 0 := by
    intro k
    induction k with
    | zero => intro m _ hmM hk; omega
    | succ k ih =>
      intro m hm1 hmM hk
      by_cases hk' : M - k ≤ m
      · exact ih m hm1 hmM hk'
      · funext z
        have hz := congrFun (hsep m (by omega)) z
        rw [Pi.zero_apply, portTotal, if_neg (by omega), add_zero,
          Finset.sum_eq_single m] at hz
        · rw [portFam, if_pos le_rfl, Nat.choose_self, Nat.sub_self, Function.iterate_zero, id,
            Nat.cast_one, mul_one] at hz
          exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ I_ne_zero)
        · intro m' hm' hne
          rw [portFam]
          by_cases hle : m ≤ m'
          · have hgt : m < m' := lt_of_le_of_ne hle (Ne.symm hne)
            rw [if_pos hle, ih m' (by omega) (Finset.mem_range.mp hm') (by omega),
              iterate_deriv_zero, Pi.zero_apply, mul_zero]
          · rw [if_neg hle]
        · intro hm; exact absurd (Finset.mem_range.mpr hmM) hm
  by_cases hM : M = 0
  · have hz := congrFun (hsep 0 (by omega)) 0
    simp [portTotal, hM] at hz
  · -- the zeroth order: the symbol of the `m = 0` port is identically one
    have h0 : ∀ z : ℂ, N 0 z = 1 := by
      intro z
      have hz := congrFun (hsep 0 (by omega)) z
      rw [Pi.zero_apply, portTotal, if_pos rfl, Finset.sum_eq_single 0] at hz
      · rw [portFam, if_pos le_rfl, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
          Nat.sub_zero, Function.iterate_zero, id, one_mul] at hz
        linear_combination hz
      · intro m hm hne
        rw [portFam, if_pos (Nat.zero_le m),
          key M m (Nat.pos_of_ne_zero hne) (Finset.mem_range.mp hm) (by omega),
          iterate_deriv_zero, Pi.zero_apply, mul_zero]
      · intro h0; exact absurd (Finset.mem_range.mpr (Nat.pos_of_ne_zero hM)) h0
    set z₀ : ℂ := ((π / 2 / h : ℝ) : ℂ) * I with hz₀
    have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh
    have hcosh : Complex.cosh (h * z₀) = 0 := by
      rw [hz₀, show (h : ℂ) * (((π / 2 / h : ℝ) : ℂ) * I) = ((π : ℂ) / 2) * I by
        push_cast; field_simp, Complex.cosh_mul_I, Complex.cos_pi_div_two]
    have h1 := h0 z₀
    rw [hNdef] at h1
    simp only [portSymbol, hcosh, mul_zero, zero_mul, Finset.sum_const_zero] at h1
    exact zero_ne_one h1

end RHTower.AnalyticPort
