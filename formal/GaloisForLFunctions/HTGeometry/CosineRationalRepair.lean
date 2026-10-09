import GaloisForLFunctions.HTGeometry.CosineAlgebraicComponents
import GaloisForLFunctions.HTGeometry.PolynomialBezoutDenominator
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Rational repairs of the cosine pair

Let `R = P/Q` be a reduced rational function of two variables and `Φ(w) = (T(w), T(-w))`.

* `Φ` is Zariski dense: a polynomial vanishing on `Φ(ℂ)` is zero.  Along
  `w = squareCoordinate (u₀ + 2πN)` the first coordinate is the fixed value `cos u₀` while the
  second coordinate is unbounded.
* An irreducible non-vertical curve meets a curve it does not divide in finitely many points
  (Gauss's lemma and a Bezout identity with polynomial denominator).
* If three distinct complete fibers of `R∘Φ` lie in `ℤ`, every irreducible factor of each pencil
  member `P - λQ` is vertical or horizontal (Theorem A), so each member is a separated product
  `A(X)B(Y)`.  A sum of two separated products is separated only if their first or their second
  factors are proportional, and pairwise coprimality of the members then forces `R ∈ ℂ(X)` or
  `R ∈ ℂ(Y)`.
* If in addition `R(Φ(-w)) R(Φ(w)) = 1`, Zariski density forces `R` to be constant: no such
  nonconstant repair exists.
-/

namespace GaloisForLFunctions.HTGeometry.CosineRationalRepair

open Complex Filter LabeledCosineDescent AlgebraicFiniteJetBranch AlgebraicReciprocalParameter
  CosineAlgebraicComponents Polynomial
open scoped Topology

noncomputable section

/-! ## Evaluation and Zariski density -/

/-- Evaluation of a bivariate polynomial at a point, as a ring homomorphism. -/
def evalHom (x y : ℂ) : BiPoly →+* ℂ :=
  (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x))

theorem evalHom_apply (P : BiPoly) (x y : ℂ) : evalHom x y P = evalAt P x y := rfl

theorem norm_cos_sq (x y : ℝ) :
    ‖Complex.cos ((x:ℂ) + (y:ℂ) * I)‖ ^ 2 = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.mul_im]
  linear_combination (Real.cos x)^2*(Real.cosh_sq y) + (Real.sinh y)^2*(Real.sin_sq_add_cos_sq x)

theorem abs_sinh_im_le_norm_cos (z : ℂ) : |Real.sinh z.im| ≤ ‖Complex.cos z‖ := by
  have hsq := norm_cos_sq z.re z.im
  rw [Complex.re_add_im] at hsq
  have h0 : 0 ≤ ‖Complex.cos z‖ := norm_nonneg _
  have : |Real.sinh z.im| ^ 2 ≤ ‖Complex.cos z‖ ^ 2 := by
    rw [sq_abs, hsq]; nlinarith [sq_nonneg (Real.cos z.re)]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) h0 (by norm_num)).mp this

/-- The second cosine coordinate along the square chart: `T(-Q(U)) = cos √(2π²/81 - U²)`. -/
theorem source_neg_squareCoordinate (U : ℂ) :
    source (-squareCoordinate U) = descendedCos (2*(Real.pi:ℂ)^2/81 - U^2) := by
  unfold source squareCoordinate
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

theorem norm_source_neg_squareCoordinate_ge (U : ℂ) :
    U.re ^ 2 - U.im ^ 2 - 2*Real.pi^2/81 ≤ ‖source (-squareCoordinate U)‖ ^ 2 := by
  rw [source_neg_squareCoordinate]
  set V := Complex.sqrt (2*(Real.pi:ℂ)^2/81 - U^2)
  have hV : V ^ 2 = 2*(Real.pi:ℂ)^2/81 - U^2 := sqrt_square _
  have hcos := abs_sinh_im_le_norm_cos V
  have hsinh : |V.im| ≤ |Real.sinh V.im| := by
    rw [Real.abs_sinh]; exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have hle : |V.im| ≤ ‖descendedCos (2*(Real.pi:ℂ)^2/81 - U^2)‖ := hsinh.trans hcos
  have hsq : V.im ^ 2 ≤ ‖descendedCos (2*(Real.pi:ℂ)^2/81 - U^2)‖ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hle 2
    rwa [sq_abs] at this
  have key : V.im ^ 2 = U.re ^ 2 - U.im ^ 2 - 2*Real.pi^2/81 + V.re ^ 2 := by
    have hc : (2*(Real.pi:ℂ)^2/81) = ((2*Real.pi^2/81 : ℝ) : ℂ) := by push_cast; ring
    have h1 := congrArg Complex.re hV
    have hU2 : (U^2).re = U.re^2 - U.im^2 := by rw [sq, Complex.mul_re]; ring
    have hV2 : (V^2).re = V.re^2 - V.im^2 := by rw [sq, Complex.mul_re]; ring
    rw [hc, Complex.sub_re, Complex.ofReal_re, hU2, hV2] at h1
    linarith
  nlinarith [sq_nonneg V.re]

/-- **Zariski density of the cosine pair.** -/
theorem eq_zero_of_vanishing_on_cosinePair (H : BiPoly)
    (h : ∀ w, evalAt H (source w) (source (-w)) = 0) : H = 0 := by
  ext i : 1
  apply Polynomial.funext
  intro a
  simp only [Polynomial.coeff_zero, Polynomial.eval_zero]
  obtain ⟨u₀, hu₀⟩ := Complex.cos_surjective a
  set U : ℕ → ℂ := fun N => u₀ + (N:ℂ) * (2*Real.pi)
  have hfirst : ∀ N, source (squareCoordinate (U N)) = a := fun N => by
    rw [source_squareCoordinate, Complex.cos_add_nat_mul_two_pi, hu₀]
  have hroot : ∀ N, (specialize H a).IsRoot (source (-squareCoordinate (U N))) := by
    intro N
    have := h (squareCoordinate (U N))
    rwa [evalAt, hfirst N] at this
  have hinf : {y : ℂ | (specialize H a).IsRoot y}.Infinite := by
    intro hfin
    obtain ⟨M, hM⟩ := hfin.isBounded.exists_norm_le
    set S := M^2 + u₀.im^2 + 2*Real.pi^2/81 + 1 + 2*|u₀.re| with hS
    obtain ⟨N, hN⟩ := exists_nat_gt (S / (2*Real.pi))
    have hge := norm_source_neg_squareCoordinate_ge (U N)
    have hM' := hM _ (hroot N)
    have hre : (U N).re = u₀.re + N*(2*Real.pi) := by simp [U]
    have him : (U N).im = u₀.im := by simp [U]
    rw [hre, him] at hge
    have hpi := Real.pi_pos
    set T : ℝ := N*(2*Real.pi) with hT
    have h1 : S < T := by
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)).mp hN
      linarith
    have h2 : ‖source (-squareCoordinate (U N))‖ ^ 2 ≤ M ^ 2 := by
      have := norm_nonneg (source (-squareCoordinate (U N)))
      nlinarith
    have hS1 : 1 + 2*|u₀.re| ≤ S := by
      have := sq_nonneg M; have := sq_nonneg u₀.im; have : 0 ≤ 2*Real.pi^2/81 := by positivity
      linarith
    have ha : -(|u₀.re| * T) ≤ u₀.re * T := by
      have := neg_abs_le u₀.re
      nlinarith [abs_nonneg u₀.re]
    have hTpos : 1 < T := by linarith [abs_nonneg u₀.re]
    have key : T * (T - 2*|u₀.re|) ≤ (u₀.re + T)^2 := by nlinarith [sq_nonneg u₀.re]
    have key2 : S - 2*|u₀.re| < T - 2*|u₀.re| := by linarith
    have key3 : (M^2 + u₀.im^2 + 2*Real.pi^2/81 + 1) * 1 < T * (T - 2*|u₀.re|) := by
      have : 0 < M^2 + u₀.im^2 + 2*Real.pi^2/81 + 1 := by positivity
      nlinarith
    nlinarith
  have hz := Polynomial.eq_zero_of_infinite_isRoot _ hinf
  have := congrArg (fun p => p.coeff i) hz
  simpa [specialize, Polynomial.coeff_map] using this

/-! ## Finite intersections of curves -/

theorem specialize_ne_zero {F : BiPoly} (hF : Irreducible F) (hd : 0 < F.natDegree) (x : ℂ) :
    specialize F x ≠ 0 := by
  intro h
  have hdiv : Polynomial.C (Polynomial.X - Polynomial.C x) ∣ F := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.dvd_iff_isRoot]
    have := congrArg (fun p => p.coeff i) h
    simpa [specialize, Polynomial.coeff_map] using this
  obtain ⟨u, hu⟩ := hdiv
  rcases hF.isUnit_or_isUnit hu with h1 | h1
  · have h2 := Polynomial.isUnit_C.mp h1
    have := Polynomial.natDegree_eq_zero_of_isUnit h2
    rw [Polynomial.natDegree_X_sub_C] at this
    exact one_ne_zero this
  · have : F.natDegree = 0 := by
      rw [hu, Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr (Polynomial.X_sub_C_ne_zero x))
        h1.ne_zero, Polynomial.natDegree_C, Polynomial.natDegree_eq_zero_of_isUnit h1]
    omega

/-- An irreducible curve of positive `Y`-degree meets a curve it does not divide in finitely many
points. -/
theorem common_zeros_finite {F Q : BiPoly} (hF : Irreducible F) (hd : 0 < F.natDegree)
    (hFQ : ¬ F ∣ Q) :
    {p : ℂ × ℂ | evalAt F p.1 p.2 = 0 ∧ evalAt Q p.1 p.2 = 0}.Finite := by
  classical
  have hprim : F.IsPrimitive := hF.isPrimitive hd.ne'
  have hirrK : Irreducible (F.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map).mp hF
  have hndvd : ¬ F.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) ∣
      Q.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
    rwa [← hprim.dvd_iff_fraction_map_dvd_fraction_map (RatFunc ℂ)]
  have hcop := (hirrK.coprime_iff_not_dvd).mpr hndvd
  obtain ⟨U, V, r, hr, hbez⟩ := exists_bezout_of_isCoprime_map (K := RatFunc ℂ) hcop
  have hsub : {p : ℂ × ℂ | evalAt F p.1 p.2 = 0 ∧ evalAt Q p.1 p.2 = 0} ⊆
      ⋃ x ∈ r.roots.toFinset, (fun y => (x, y)) '' (specialize F x).roots.toFinset := by
    rintro ⟨x, y⟩ ⟨h1, h2⟩
    have hx : r.eval x = 0 := by
      have := congrArg (evalHom x y) hbez
      simp only [map_add, map_mul, evalHom_apply, h1, h2, mul_zero, add_zero] at this
      simpa [evalAt, specialize, Polynomial.eval_map] using this.symm
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Multiset.mem_toFinset]
    refine ⟨x, (Polynomial.mem_roots hr).mpr hx, y, ?_, rfl⟩
    exact (Polynomial.mem_roots (specialize_ne_zero hF hd x)).mpr h1
  refine Set.Finite.subset ?_ hsub
  exact Set.Finite.biUnion (Finset.finite_toSet _) (fun x _ => (Finset.finite_toSet _).image _)

/-! ## Integral fibers force coordinate factors -/

/-- `λ`-fibre of `R∘Φ` inside the integers. -/
def FiberIntegral (P Q : BiPoly) (lam : ℂ) : Prop :=
  ∀ w : ℂ, evalAt Q (source w) (source (-w)) ≠ 0 →
    evalAt P (source w) (source (-w)) = lam * evalAt Q (source w) (source (-w)) →
      w ∈ Set.range (Int.cast : ℤ → ℂ)

/-- The pencil member `P - λQ`. -/
def pencil (P Q : BiPoly) (lam : ℂ) : BiPoly := P - Polynomial.C (Polynomial.C lam) * Q

theorem evalAt_pencil (P Q : BiPoly) (lam x y : ℂ) :
    evalAt (pencil P Q lam) x y = evalAt P x y - lam * evalAt Q x y := by
  rw [← evalHom_apply, pencil]; simp [evalHom_apply, evalAt, specialize]

theorem eq_pencil_add (P Q : BiPoly) (l : ℂ) :
    P = pencil P Q l + Polynomial.C (Polynomial.C l) * Q := by
  rw [pencil]; ring

/-- Every irreducible factor of a member of an integral fibre is vertical or horizontal. -/
theorem factor_coordinate {P Q : BiPoly} (hrel : IsRelPrime P Q) {lam : ℂ}
    (hfib : FiberIntegral P Q lam) {F : BiPoly} (hF : Irreducible F) (hFM : F ∣ pencil P Q lam) :
    F.natDegree = 0 ∨ parameterDegree F = 0 := by
  by_contra h
  push Not at h
  obtain ⟨hy, hx⟩ := h
  have hy' : 0 < F.natDegree := Nat.pos_of_ne_zero hy
  have hx' : 0 < parameterDegree F := Nat.pos_of_ne_zero hx
  have hFQ : ¬ F ∣ Q := by
    intro hQ
    have hP : F ∣ P := by
      rw [eq_pencil_add P Q lam]; exact dvd_add hFM (dvd_mul_of_dvd_right hQ _)
    exact hF.not_isUnit (hrel hP hQ)
  have hfin := common_zeros_finite hF hy' hFQ
  obtain ⟨w, hw⟩ := (offIntegerFiber_infinite F hF hx' hy' hfin.toFinset).nonempty
  obtain ⟨hFw, hB, hZ⟩ := hw
  have hQw : evalAt Q (source w) (source (-w)) ≠ 0 := by
    intro hQ0
    exact hB (hfin.mem_toFinset.mpr ⟨hFw, hQ0⟩)
  obtain ⟨G, hG⟩ := hFM
  have hMw : evalAt (pencil P Q lam) (source w) (source (-w)) = 0 := by
    rw [hG, ← evalHom_apply, map_mul, evalHom_apply, hFw, zero_mul]
  rw [evalAt_pencil, sub_eq_zero] at hMw
  exact hZ (hfib w hQw hMw)

/-- A separated product `A(X)·B(Y)`. -/
def IsSeparated (M : BiPoly) : Prop :=
  ∃ a b : Polynomial ℂ, M = Polynomial.C a * b.map Polynomial.C

theorem eq_map_C_of_parameterDegree_eq_zero {F : BiPoly} (h : parameterDegree F = 0) :
    F = (F.map Polynomial.constantCoeff).map Polynomial.C := by
  ext k : 1
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  have hk : (F.coeff k).natDegree = 0 := by
    have := coeff_natDegree_le_parameterDegree F k; omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hk]
  simp

theorem separated_of_factors (M : BiPoly) (hM : M ≠ 0)
    (h : ∀ F, Irreducible F → F ∣ M → F.natDegree = 0 ∨ parameterDegree F = 0) : IsSeparated M := by
  induction M using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd rfl hM
  | unit u hu =>
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hu
    exact ⟨r, 1, by simp⟩
  | mul a i ha hi ih =>
    obtain ⟨a', b', hab⟩ := ih ha (fun F hF hFa => h F hF (dvd_mul_of_dvd_right hFa i))
    rcases h i hi (dvd_mul_right i a) with hi0 | hi0
    · refine ⟨i.coeff 0 * a', b', ?_⟩
      conv_lhs => rw [hab, Polynomial.eq_C_of_natDegree_eq_zero hi0]
      rw [map_mul]; ring
    · refine ⟨a', (i.map Polynomial.constantCoeff) * b', ?_⟩
      rw [hab, Polynomial.map_mul, ← eq_map_C_of_parameterDegree_eq_zero hi0]; ring

/-- Specializing the parameter of a separated product. -/
theorem specialize_separated (a b : Polynomial ℂ) (x : ℂ) :
    specialize (Polynomial.C a * b.map Polynomial.C) x = Polynomial.C (a.eval x) * b := by
  have hc : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℂ := by ext; simp
  simp [specialize, Polynomial.map_map, hc]

theorem specialize_add (F G : BiPoly) (x : ℂ) :
    specialize (F + G) x = specialize F x + specialize G x := Polynomial.map_add _

/-- **Decomposable tensors.**  If `a₁⊗b₁ + a₂⊗b₂ = a₃⊗b₃` with `a₁, b₁ ≠ 0`, then the first or the
second factors of the two summands are proportional. -/
theorem separated_sum {a₁ a₂ a₃ b₁ b₂ b₃ : Polynomial ℂ} (ha : a₁ ≠ 0) (hb : b₁ ≠ 0)
    (h : Polynomial.C a₁ * b₁.map Polynomial.C + Polynomial.C a₂ * b₂.map Polynomial.C =
      Polynomial.C a₃ * b₃.map Polynomial.C) :
    (∃ κ : ℂ, a₂ = Polynomial.C κ * a₁) ∨ (∃ κ : ℂ, b₂ = Polynomial.C κ * b₁) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨x₂, hx₂⟩ : ∃ x, a₁.eval x ≠ 0 := by
    by_contra hall; push Not at hall
    exact ha (Polynomial.funext (fun x => by simp [hall x]))
  obtain ⟨x₁, hx₁⟩ : ∃ x, a₁.eval x * a₂.eval x₂ - a₁.eval x₂ * a₂.eval x ≠ 0 := by
    by_contra hall; push Not at hall
    apply hA (a₂.eval x₂ / a₁.eval x₂)
    apply Polynomial.funext
    intro x
    have := hall x
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    field_simp
    linear_combination -this
  have e₁ := congrArg (fun F => specialize F x₁) h
  have e₂ := congrArg (fun F => specialize F x₂) h
  simp only [specialize_add, specialize_separated] at e₁ e₂
  obtain ⟨D, hD⟩ : ∃ D, D = a₁.eval x₁ * a₂.eval x₂ - a₁.eval x₂ * a₂.eval x₁ := ⟨_, rfl⟩
  rw [← hD] at hx₁
  set α := a₃.eval x₁ * a₂.eval x₂ - a₃.eval x₂ * a₂.eval x₁ with hα_def
  set β := a₁.eval x₁ * a₃.eval x₂ - a₁.eval x₂ * a₃.eval x₁ with hβ_def
  have h1 : Polynomial.C D * b₁ = Polynomial.C α * b₃ := by
    simp only [hD, hα_def, map_sub, map_mul]
    linear_combination Polynomial.C (a₂.eval x₂) * e₁ - Polynomial.C (a₂.eval x₁) * e₂
  have h2 : Polynomial.C D * b₂ = Polynomial.C β * b₃ := by
    simp only [hD, hβ_def, map_sub, map_mul]
    linear_combination Polynomial.C (a₁.eval x₁) * e₂ - Polynomial.C (a₁.eval x₂) * e₁
  have hα : α ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_mul] at h1
    exact hb ((mul_eq_zero.mp h1).resolve_left (Polynomial.C_ne_zero.mpr hx₁))
  apply hB (β / α)
  apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hx₁)
  rw [h2, mul_left_comm, h1, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hα]

/-! ## Three integral fibres -/

theorem parameterDegree_map_C (b : Polynomial ℂ) : parameterDegree (b.map Polynomial.C) = 0 := by
  unfold parameterDegree
  apply Finset.sup_eq_bot_iff _ _ |>.mpr
  intro i _
  simp [Polynomial.coeff_map]

private theorem pencil_sub (P Q : BiPoly) (l m : ℂ) :
    pencil P Q l - pencil P Q m = Polynomial.C (Polynomial.C (m - l)) * Q := by
  simp only [pencil, map_sub]; ring

private theorem divides_P_Q {P Q X : BiPoly} {l m : ℂ} (hlm : l ≠ m)
    (h₁ : X ∣ pencil P Q l) (h₂ : X ∣ pencil P Q m) : X ∣ P ∧ X ∣ Q := by
  have hQ : X ∣ Q := by
    have h := dvd_sub h₁ h₂
    rw [pencil_sub] at h
    have hu : IsUnit (Polynomial.C (Polynomial.C (m - l)) : BiPoly) :=
      Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (sub_ne_zero.mpr hlm.symm).isUnit)
    exact (hu.dvd_mul_left).mp h
  refine ⟨?_, hQ⟩
  rw [eq_pencil_add P Q l]; exact dvd_add h₁ (dvd_mul_of_dvd_right hQ _)

/-- **Three integral fibres.**  If three distinct fibres of `P/Q ∘ Φ` (with `P, Q` relatively prime)
lie in `ℤ`, then `P/Q` depends on one coordinate only: `P, Q ∈ ℂ[X]` or `P, Q ∈ ℂ[Y]`. -/
theorem three_integral_fibers {P Q : BiPoly} (hrel : IsRelPrime P Q) (lam : Fin 3 → ℂ)
    (hlam : Function.Injective lam) (hfib : ∀ j, FiberIntegral P Q (lam j)) :
    (P.natDegree = 0 ∧ Q.natDegree = 0) ∨ (parameterDegree P = 0 ∧ parameterDegree Q = 0) := by
  by_cases hz : ∃ j, pencil P Q (lam j) = 0
  · obtain ⟨j, hj⟩ := hz
    have hPQ : P = Polynomial.C (Polynomial.C (lam j)) * Q := by
      rw [pencil, sub_eq_zero] at hj; exact hj
    have hQu : IsUnit Q := hrel ⟨_, by rw [hPQ, mul_comm]⟩ dvd_rfl
    left
    have hQ0 := Polynomial.natDegree_eq_zero_of_isUnit hQu
    refine ⟨?_, hQ0⟩
    rw [hPQ]
    exact Nat.le_zero.mp ((Polynomial.natDegree_C_mul_le _ _).trans hQ0.le)
  · push Not at hz
    have hsep : ∀ j, ∃ a b : Polynomial ℂ, a ≠ 0 ∧ b ≠ 0 ∧
        pencil P Q (lam j) = Polynomial.C a * b.map Polynomial.C := by
      intro j
      obtain ⟨a, b, hab⟩ := separated_of_factors _ (hz j)
        (fun F hF hFM => factor_coordinate hrel (hfib j) hF hFM)
      refine ⟨a, b, ?_, ?_, hab⟩
      · rintro rfl; exact hz j (by simp [hab])
      · rintro rfl; exact hz j (by simp [hab])
    obtain ⟨a₀, b₀, ha₀, hb₀, h₀⟩ := hsep 0
    obtain ⟨a₁, b₁, ha₁, hb₁, h₁⟩ := hsep 1
    obtain ⟨a₂, b₂, ha₂, hb₂, h₂⟩ := hsep 2
    have h01 : lam 0 ≠ lam 1 := fun h => by simpa using hlam h
    have h12 : lam 1 ≠ lam 2 := fun h => by simpa using hlam h
    have h20 : lam 2 ≠ lam 0 := fun h => by simpa using hlam h
    set d₀ := lam 1 - lam 2
    set d₁ := lam 2 - lam 0
    set d₂ := lam 0 - lam 1
    have hd₀ : d₀ ≠ 0 := sub_ne_zero.mpr h12
    have hd₁ : d₁ ≠ 0 := sub_ne_zero.mpr h20
    have hrelation : Polynomial.C (Polynomial.C d₀ * a₀) * b₀.map Polynomial.C +
        Polynomial.C (Polynomial.C d₁ * a₁) * b₁.map Polynomial.C =
        Polynomial.C (-(Polynomial.C d₂ * a₂)) * b₂.map Polynomial.C := by
      have e : (Polynomial.C (Polynomial.C d₀) : BiPoly) * pencil P Q (lam 0) +
          Polynomial.C (Polynomial.C d₁) * pencil P Q (lam 1) +
          Polynomial.C (Polynomial.C d₂) * pencil P Q (lam 2) = 0 := by
        simp only [pencil, d₀, d₁, d₂, map_sub]; ring
      rw [h₀, h₁, h₂] at e
      simp only [map_mul, map_neg]
      linear_combination e
    rcases separated_sum (mul_ne_zero (Polynomial.C_ne_zero.mpr hd₀) ha₀) hb₀ hrelation with
      ⟨κ, hκ⟩ | ⟨κ, hκ⟩
    · -- proportional first factors: the common factor `C a₀` is a unit
      have ha₁' : a₁ = Polynomial.C (κ * d₀ / d₁) * a₀ := by
        apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hd₁)
        rw [hκ, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
        congr 2; field_simp
      have hd0 : (Polynomial.C a₀ : BiPoly) ∣ pencil P Q (lam 0) := ⟨_, h₀⟩
      have hd1 : (Polynomial.C a₀ : BiPoly) ∣ pencil P Q (lam 1) :=
        ⟨Polynomial.C (Polynomial.C (κ * d₀ / d₁)) * b₁.map Polynomial.C, by
          rw [h₁, ha₁', map_mul]; ring⟩
      obtain ⟨hP, hQ⟩ := divides_P_Q h01 hd0 hd1
      have hu : IsUnit a₀ := Polynomial.isUnit_C.mp (hrel hP hQ)
      obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.mp hu
      right
      have hM0 : pencil P Q (lam 0) = (Polynomial.C c * b₀).map Polynomial.C := by
        rw [h₀, ← hc, Polynomial.map_mul, Polynomial.map_C]
      have hM1 : pencil P Q (lam 1) =
          (Polynomial.C (κ * d₀ / d₁ * c) * b₁).map Polynomial.C := by
        rw [h₁, ha₁', ← hc, Polynomial.map_mul, Polynomial.map_C, ← map_mul]
      have hQform : Q = (Polynomial.C (1/(lam 1 - lam 0)) *
          (Polynomial.C c * b₀ - Polynomial.C (κ * d₀ / d₁ * c) * b₁)).map Polynomial.C := by
        have e := pencil_sub P Q (lam 0) (lam 1)
        rw [hM0, hM1, ← Polynomial.map_sub] at e
        have hne : lam 1 - lam 0 ≠ 0 := sub_ne_zero.mpr h01.symm
        rw [Polynomial.map_mul, e, Polynomial.map_C, ← mul_assoc, ← map_mul, ← map_mul]
        rw [show 1 / (lam 1 - lam 0) * (lam 1 - lam 0) = 1 by field_simp]; simp
      have hPform : P = ((Polynomial.C c * b₀) + Polynomial.C (lam 0) *
          (Polynomial.C (1/(lam 1 - lam 0)) *
            (Polynomial.C c * b₀ - Polynomial.C (κ * d₀ / d₁ * c) * b₁))).map Polynomial.C := by
        rw [eq_pencil_add P Q (lam 0), hM0, hQform]
        simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
      exact ⟨hPform ▸ parameterDegree_map_C _, hQform ▸ parameterDegree_map_C _⟩
    · -- proportional second factors: the common factor `map C b₀` is a unit
      have hd0 : (b₀.map Polynomial.C : BiPoly) ∣ pencil P Q (lam 0) := ⟨_, by rw [h₀, mul_comm]⟩
      have hd1 : (b₀.map Polynomial.C : BiPoly) ∣ pencil P Q (lam 1) :=
        ⟨Polynomial.C (Polynomial.C κ * a₁), by
          rw [h₁, hκ, Polynomial.map_mul, Polynomial.map_C, map_mul]; ring⟩
      obtain ⟨hP, hQ⟩ := divides_P_Q h01 hd0 hd1
      have hu : IsUnit (b₀.map Polynomial.C : BiPoly) := hrel hP hQ
      have hb0deg : b₀.natDegree = 0 := by
        have := Polynomial.natDegree_eq_zero_of_isUnit hu
        rwa [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective] at this
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hb0deg
      have hb1deg : b₁.natDegree = 0 := by
        rw [hκ, ← hc, ← map_mul]; exact Polynomial.natDegree_C _
      left
      have hM0 : (pencil P Q (lam 0)).natDegree = 0 := by
        rw [h₀]
        exact Nat.le_zero.mp ((Polynomial.natDegree_C_mul_le _ _).trans
          (by rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, hb0deg]))
      have hM1 : (pencil P Q (lam 1)).natDegree = 0 := by
        rw [h₁]
        exact Nat.le_zero.mp ((Polynomial.natDegree_C_mul_le _ _).trans
          (by rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, hb1deg]))
      have hne : lam 1 - lam 0 ≠ 0 := sub_ne_zero.mpr h01.symm
      have hQform : Q = Polynomial.C (Polynomial.C (1/(lam 1 - lam 0))) *
          (pencil P Q (lam 0) - pencil P Q (lam 1)) := by
        rw [pencil_sub, ← mul_assoc, ← map_mul, ← map_mul,
          show 1 / (lam 1 - lam 0) * (lam 1 - lam 0) = 1 by field_simp]; simp
      have hQ0 : Q.natDegree = 0 := by
        rw [hQform]
        refine Nat.le_zero.mp ((Polynomial.natDegree_C_mul_le _ _).trans ?_)
        exact (Polynomial.natDegree_sub_le _ _).trans (by rw [hM0, hM1]; simp)
      have hP0 : P.natDegree = 0 := by
        rw [eq_pencil_add P Q (lam 0)]
        refine Nat.le_zero.mp ((Polynomial.natDegree_add_le _ _).trans ?_)
        rw [hM0]
        exact max_le le_rfl ((Polynomial.natDegree_C_mul_le _ _).trans hQ0.le)
      exact ⟨hP0, hQ0⟩

/-! ## No reciprocal repair -/

theorem evalAt_sub (F G : BiPoly) (x y : ℂ) :
    evalAt (F - G) x y = evalAt F x y - evalAt G x y := by
  simp [evalAt, specialize]

private theorem proportional_of_reciprocal {a c : Polynomial ℂ} (hc : c ≠ 0)
    (h : ∀ w, c.eval (source w) ≠ 0 → c.eval (source (-w)) ≠ 0 →
      a.eval (source w) * a.eval (source (-w)) = c.eval (source w) * c.eval (source (-w))) :
    ∃ κ : ℂ, a = Polynomial.C κ * c := by
  set H : BiPoly := Polynomial.C a * a.map Polynomial.C - Polynomial.C c * c.map Polynomial.C
  set D : BiPoly := Polynomial.C c * c.map Polynomial.C
  have hev : ∀ (b d : Polynomial ℂ) (x y : ℂ),
      evalAt (Polynomial.C b * d.map Polynomial.C) x y = b.eval x * d.eval y := by
    intro b d x y
    rw [evalAt, specialize_separated, Polynomial.eval_mul, Polynomial.eval_C]
  have hvan : H * D = 0 := by
    apply eq_zero_of_vanishing_on_cosinePair
    intro w
    rw [← evalHom_apply, map_mul, evalHom_apply, evalHom_apply]
    by_cases h1 : c.eval (source w) = 0
    · simp [D, hev, h1]
    by_cases h2 : c.eval (source (-w)) = 0
    · simp [D, hev, h2]
    rw [evalAt_sub, hev, hev, h w h1 h2, sub_self, zero_mul]
  have hD : D ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc)
    (Polynomial.map_ne_zero_iff Polynomial.C_injective |>.mpr hc)
  have hH : H = 0 := (mul_eq_zero.mp hvan).resolve_right hD
  have hxy : ∀ x y, a.eval x * a.eval y = c.eval x * c.eval y := by
    intro x y
    have := congrArg (fun F => evalAt F x y) hH
    simp only [H] at this
    rw [evalAt_sub, hev, hev] at this
    simpa [evalAt, specialize, sub_eq_zero] using this
  obtain ⟨y₀, hy₀⟩ : ∃ y, c.eval y ≠ 0 := by
    by_contra hall; push Not at hall
    exact hc (Polynomial.funext (fun x => by simp [hall x]))
  have ha₀ : a.eval y₀ ≠ 0 := by
    intro h0
    apply hc; apply Polynomial.funext; intro x
    have := hxy x y₀
    rw [h0, mul_zero] at this
    simpa [hy₀] using this.symm
  refine ⟨c.eval y₀ / a.eval y₀, Polynomial.funext (fun x => ?_)⟩
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  field_simp
  linear_combination hxy x y₀

private theorem degrees_of_isUnit {Q : BiPoly} (hQ : IsUnit Q) :
    Q.natDegree = 0 ∧ parameterDegree Q = 0 := by
  obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hQ
  obtain ⟨u, -, rfl⟩ := Polynomial.isUnit_iff.mp hr
  exact ⟨Polynomial.natDegree_C _, by
    unfold parameterDegree
    exact Finset.sup_eq_bot_iff _ _ |>.mpr (fun i _ => by
      rw [Polynomial.coeff_C]; split_ifs <;> simp)⟩

/-- **No reciprocal repair.**  No nonconstant reduced rational function `R = P/Q` has three distinct
fibres of `R∘Φ` inside `ℤ` together with `R(Φ(-w)) R(Φ(w)) = 1`. -/
theorem no_reciprocal_repair {P Q : BiPoly} (hrel : IsRelPrime P Q) (hQ : Q ≠ 0)
    (hnc : ¬ (P.natDegree = 0 ∧ parameterDegree P = 0 ∧ Q.natDegree = 0 ∧ parameterDegree Q = 0))
    (lam : Fin 3 → ℂ) (hlam : Function.Injective lam) (hfib : ∀ j, FiberIntegral P Q (lam j))
    (hrec : ∀ w, evalAt Q (source w) (source (-w)) ≠ 0 → evalAt Q (source (-w)) (source w) ≠ 0 →
      evalAt P (source (-w)) (source w) / evalAt Q (source (-w)) (source w) *
        (evalAt P (source w) (source (-w)) / evalAt Q (source w) (source (-w))) = 1) : False := by
  have hcollapse : ∀ κ : ℂ, P = Polynomial.C (Polynomial.C κ) * Q → False := by
    intro κ hPQ
    have hu : IsUnit Q := hrel ⟨_, by rw [hPQ, mul_comm]⟩ dvd_rfl
    obtain ⟨hQ1, hQ2⟩ := degrees_of_isUnit hu
    obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hu
    apply hnc
    rw [hPQ]
    refine ⟨Nat.le_zero.mp ((Polynomial.natDegree_C_mul_le _ _).trans hQ1.le), ?_, hQ1, hQ2⟩
    rw [← hr, ← map_mul]
    unfold parameterDegree
    refine Finset.sup_eq_bot_iff _ _ |>.mpr (fun i _ => ?_)
    rw [Polynomial.coeff_C]; split_ifs
    · obtain ⟨u, -, rfl⟩ := Polynomial.isUnit_iff.mp (Polynomial.isUnit_C.mp (hr ▸ hu))
      simp [← map_mul]
    · simp
  rcases three_integral_fibers hrel lam hlam hfib with ⟨hP0, hQ0⟩ | ⟨hP0, hQ0⟩
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hP0] at hrec hcollapse
    rw [Polynomial.eq_C_of_natDegree_eq_zero hQ0] at hrec hcollapse hQ
    have hc : Q.coeff 0 ≠ 0 := fun h => hQ (by rw [h, map_zero])
    have hev : ∀ (b : Polynomial ℂ) (x y : ℂ), evalAt (Polynomial.C b) x y = b.eval x := by
      intro b x y; simp [evalAt, specialize]
    obtain ⟨κ, hκ⟩ := proportional_of_reciprocal (a := P.coeff 0) hc (fun w h1 h2 => by
      have := hrec w (by rwa [hev]) (by rwa [hev])
      simp only [hev] at this
      field_simp at this
      linear_combination this)
    exact hcollapse κ (by simp [hκ, map_mul])
  · rw [eq_map_C_of_parameterDegree_eq_zero hP0] at hrec hcollapse
    rw [eq_map_C_of_parameterDegree_eq_zero hQ0] at hrec hcollapse hQ
    have hc : Q.map Polynomial.constantCoeff ≠ 0 := fun h => hQ (by rw [h, Polynomial.map_zero])
    have hev : ∀ (b : Polynomial ℂ) (x y : ℂ), evalAt (b.map Polynomial.C) x y = b.eval y := by
      intro b x y
      have hcomp : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℂ := by ext; simp
      simp [evalAt, specialize, Polynomial.map_map, hcomp]
    obtain ⟨κ, hκ⟩ := proportional_of_reciprocal (a := P.map Polynomial.constantCoeff) hc
      (fun w h1 h2 => by
        have := hrec w (by rw [hev]; exact h2) (by rw [hev]; exact h1)
        simp only [hev] at this
        field_simp at this
        linear_combination this)
    exact hcollapse κ (by simp [hκ, Polynomial.map_mul, Polynomial.map_C])

end
end GaloisForLFunctions.HTGeometry.CosineRationalRepair
