import GaloisForLFunctions.FamilyContinuationTheory.TheSexticGaussSumsAreTwistedMultiplicative

/-!
# The Poisson coefficient is multiplicative up to reciprocity

Poisson summation of the cubic-theta probe in its element variable `m` produces, for a row twist
`s` and an index `A`, the coefficient

`F(s, A; H) = Σ_{m mod sA} χ_A(m) g_s(−m) ψ_{sA}(Hm)`   (`poissonCoeff`),

the finite Fourier transform of `m ↦ χ_A(m) g_s(−m)` modulo `sA` at the frequency `H`. For a
coprime splitting `s = s₁s₂`, `A = A₁A₂`, `(s₁A₁, s₂A₂) = 1`:

* `poissonCoeff_mul`: `χ_{s₁}(s₂A₂) χ_{s₂}(s₁A₁) F(s, A; H) =
  χ_{s₁}(s₂) χ_{s₂}(s₁) χ_{A₁}(s₂A₂) χ_{A₂}(s₁A₁) F(s₁, A₁; H) F(s₂, A₂; H)`;
* `poissonCoeff_mul_reciprocity`: for primary indices prime to `2`,
  `F(s, A; H) = r(A₁, s₂) r(A₂, s₁) χ_{A₁}(A₂) χ_{A₂}(A₁) F(s₁, A₁; H) F(s₂, A₂; H)`.

The phases between the row twists cancel exactly; sextic reciprocity turns the phases between a
twist and an index into the sign `r`, which the probe's fixed ray bicharacter `R(A, s)` removes.
The remaining phase between the indices is cancelled by the theta coefficients of `A`.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-! ### Fourier transforms through residue representatives -/

/-- The finite Fourier transform modulo `N` of `f`, read on residue representatives. -/
def residueFourier (N : O) [NeZero N] (f : O → ℂ) (H : O) : ℂ :=
  ∑ m : O ⧸ Ideal.span {N}, f (qrep m) * principalTraceChar N (NeZero.ne N)
    (Ideal.Quotient.mk _ H * m)

/-- The transform depends only on the element `N`. -/
theorem residueFourier_congr {N N' : O} [NeZero N] [NeZero N'] (h : N = N') (f : O → ℂ) (H : O) :
    residueFourier N f H = residueFourier N' f H := by
  subst h
  rfl

/-- A function is periodic modulo `N`. -/
def IsPeriodic (N : O) (f : O → ℂ) : Prop := ∀ x y : O, N ∣ x - y → f x = f y

/-- **CRT for transforms.** For coprime `M₁, M₂` and `f₁, f₂` periodic modulo `M₁, M₂`,
`F_{M₁M₂}(f₁ f₂)(H) = F_{M₁}(x ↦ f₁(M₂x))(H) · F_{M₂}(y ↦ f₂(M₁y))(H)`. -/
theorem residueFourier_mul (M₁ M₂ : O) [NeZero M₁] [NeZero M₂] (h12 : IsCoprime M₁ M₂)
    {f₁ f₂ : O → ℂ} (hf₁ : IsPeriodic M₁ f₁) (hf₂ : IsPeriodic M₂ f₂) (H : O) :
    haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne M₁) (NeZero.ne M₂)⟩
    residueFourier (M₁ * M₂) (fun m => f₁ m * f₂ m) H =
      residueFourier M₁ (fun x => f₁ (M₂ * x)) H * residueFourier M₂ (fun y => f₂ (M₁ * y)) H := by
  haveI : NeZero (M₁ * M₂) := ⟨mul_ne_zero (NeZero.ne M₁) (NeZero.ne M₂)⟩
  have hl : ∀ m : O ⧸ Ideal.span {M₁ * M₂}, f₁ (qrep m) = f₁ (qrep (reduceLeft M₁ M₂ m)) := by
    intro m
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    apply hf₁
    have h1 : M₁ * M₂ ∣ qrep (Ideal.Quotient.mk (Ideal.span {M₁ * M₂}) x) - x := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep]
    have h2 : M₁ ∣ qrep (reduceLeft M₁ M₂ (Ideal.Quotient.mk _ x)) - x := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep]
      rfl
    have h3 := dvd_sub ((dvd_mul_right M₁ M₂).trans h1) h2
    rwa [sub_sub_sub_cancel_right] at h3
  have hr : ∀ m : O ⧸ Ideal.span {M₁ * M₂}, f₂ (qrep m) = f₂ (qrep (reduceRight M₁ M₂ m)) := by
    intro m
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    apply hf₂
    have h1 : M₁ * M₂ ∣ qrep (Ideal.Quotient.mk (Ideal.span {M₁ * M₂}) x) - x := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep]
    have h2 : M₂ ∣ qrep (reduceRight M₁ M₂ (Ideal.Quotient.mk _ x)) - x := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep]
      rfl
    have h3 := dvd_sub ((dvd_mul_left M₂ M₁).trans h1) h2
    rwa [sub_sub_sub_cancel_right] at h3
  unfold residueFourier
  simp only [hl, hr]
  rw [sum_crt_mul_traceChar M₁ M₂ h12 (fun x => f₁ (qrep x)) (fun y => f₂ (qrep y)) H]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    apply hf₁
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep, map_mul, mk_qrep]
  · refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    apply hf₂
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, mk_qrep, map_mul, mk_qrep]

theorem residueFourier_const_mul (N : O) [NeZero N] (c : ℂ) (f : O → ℂ) (H : O) :
    residueFourier N (fun m => c * f m) H = c * residueFourier N f H := by
  unfold residueFourier
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem residueFourier_congr_fun (N : O) [NeZero N] {f g : O → ℂ} (h : ∀ m, f m = g m) (H : O) :
    residueFourier N f H = residueFourier N g H := by
  unfold residueFourier
  simp only [h]

/-! ### The Poisson coefficient -/

/-- The sextic Gauss sum depends on its frequency modulo `c`. -/
theorem sexticGauss_congr (c : O) [NeZero c] {x y : O} (hxy : c ∣ x - y) :
    sexticGauss c x = sexticGauss c y := by
  unfold sexticGauss
  rw [(Ideal.Quotient.eq).mpr (Ideal.mem_span_singleton.mpr hxy)]

/-- The Poisson coefficient `F(s, A; H) = Σ_{m mod sA} χ_A(m) g_s(−m) ψ_{sA}(Hm)`. -/
def poissonCoeff (s A : O) [NeZero s] [NeZero A] (H : O) : ℂ :=
  residueFourier (s * A) (fun m => sexticSymbol m A * sexticGauss s (-m)) H

/-- The summand of the Poisson coefficient is periodic modulo `sA`. -/
theorem isPeriodic_poissonSummand (s A : O) [NeZero s] :
    IsPeriodic (s * A) fun m => sexticSymbol m A * sexticGauss s (-m) := by
  intro x y hxy
  have hA : A ∣ x - y := (dvd_mul_left A s).trans hxy
  have hs : s ∣ -x - -y := by
    rw [neg_sub_neg]
    exact dvd_sub_comm.mp ((dvd_mul_right s A).trans hxy)
  show sexticSymbol x A * sexticGauss s (-x) = sexticSymbol y A * sexticGauss s (-y)
  rw [sexticSymbol_congr hA, sexticGauss_congr s hs]

/-- **Multiplicativity of the Poisson coefficient.** For a coprime splitting `s = s₁s₂`,
`A = A₁A₂` with `(s₁A₁, s₂A₂) = 1`:
`χ_{s₁}(s₂A₂) χ_{s₂}(s₁A₁) F(s, A; H) =
  χ_{s₁}(s₂) χ_{s₂}(s₁) χ_{A₁}(s₂A₂) χ_{A₂}(s₁A₁) F(s₁, A₁; H) F(s₂, A₂; H)`. -/
theorem poissonCoeff_mul (s₁ s₂ A₁ A₂ : O) [NeZero s₁] [NeZero s₂] [NeZero A₁] [NeZero A₂]
    (h12 : IsCoprime (s₁ * A₁) (s₂ * A₂)) (H : O) :
    sexticSymbol (s₂ * A₂) s₁ * sexticSymbol (s₁ * A₁) s₂ * poissonCoeff (s₁ * s₂) (A₁ * A₂) H =
      sexticSymbol s₂ s₁ * sexticSymbol s₁ s₂ * sexticSymbol (s₂ * A₂) A₁ *
        sexticSymbol (s₁ * A₁) A₂ * poissonCoeff s₁ A₁ H * poissonCoeff s₂ A₂ H := by
  have hs12 : IsCoprime s₁ s₂ :=
    (h12.of_isCoprime_of_dvd_left (dvd_mul_right s₁ A₁)).of_isCoprime_of_dvd_right
      (dvd_mul_right s₂ A₂)
  have hM2s1 : IsCoprime (s₂ * A₂) s₁ := (h12.of_isCoprime_of_dvd_left (dvd_mul_right s₁ A₁)).symm
  have hM1s2 : IsCoprime (s₁ * A₁) s₂ := h12.of_isCoprime_of_dvd_right (dvd_mul_right s₂ A₂)
  -- the summand splits
  have hsplit : ∀ m : O, sexticSymbol m (A₁ * A₂) * sexticGauss (s₁ * s₂) (-m) =
      (sexticSymbol s₂ s₁ * sexticSymbol s₁ s₂) *
        ((sexticSymbol m A₁ * sexticGauss s₁ (-m)) * (sexticSymbol m A₂ * sexticGauss s₂ (-m))) := by
    intro m
    rw [sexticSymbol_mul_denominator, sexticGauss_mul s₁ s₂ hs12]
    ring
  -- each local factor absorbs the cofactor
  have hloc₁ : ∀ x : O, sexticSymbol (s₂ * A₂) s₁ *
      (sexticSymbol (s₂ * A₂ * x) A₁ * sexticGauss s₁ (-(s₂ * A₂ * x))) =
      sexticSymbol (s₂ * A₂) A₁ * (sexticSymbol x A₁ * sexticGauss s₁ (-x)) := by
    intro x
    have h := sexticSymbol_mul_sexticGauss s₁ hM2s1 (-x)
    rw [show s₂ * A₂ * -x = -(s₂ * A₂ * x) by ring] at h
    rw [sexticSymbol_mul_numerator (s₂ * A₂) x A₁, ← h]
    ring
  have hloc₂ : ∀ y : O, sexticSymbol (s₁ * A₁) s₂ *
      (sexticSymbol (s₁ * A₁ * y) A₂ * sexticGauss s₂ (-(s₁ * A₁ * y))) =
      sexticSymbol (s₁ * A₁) A₂ * (sexticSymbol y A₂ * sexticGauss s₂ (-y)) := by
    intro y
    have h := sexticSymbol_mul_sexticGauss s₂ hM1s2 (-y)
    rw [show s₁ * A₁ * -y = -(s₁ * A₁ * y) by ring] at h
    rw [sexticSymbol_mul_numerator (s₁ * A₁) y A₂, ← h]
    ring
  unfold poissonCoeff
  rw [residueFourier_congr (show s₁ * s₂ * (A₁ * A₂) = (s₁ * A₁) * (s₂ * A₂) by ring),
    residueFourier_congr_fun _ hsplit, residueFourier_const_mul,
    residueFourier_mul (s₁ * A₁) (s₂ * A₂) h12 (isPeriodic_poissonSummand s₁ A₁)
      (isPeriodic_poissonSummand s₂ A₂)]
  have e₁ : sexticSymbol (s₂ * A₂) s₁ * residueFourier (s₁ * A₁)
      (fun x => sexticSymbol (s₂ * A₂ * x) A₁ * sexticGauss s₁ (-(s₂ * A₂ * x))) H =
      sexticSymbol (s₂ * A₂) A₁ * residueFourier (s₁ * A₁)
        (fun x => sexticSymbol x A₁ * sexticGauss s₁ (-x)) H := by
    rw [← residueFourier_const_mul, ← residueFourier_const_mul]
    exact residueFourier_congr_fun _ hloc₁ H
  have e₂ : sexticSymbol (s₁ * A₁) s₂ * residueFourier (s₂ * A₂)
      (fun y => sexticSymbol (s₁ * A₁ * y) A₂ * sexticGauss s₂ (-(s₁ * A₁ * y))) H =
      sexticSymbol (s₁ * A₁) A₂ * residueFourier (s₂ * A₂)
        (fun y => sexticSymbol y A₂ * sexticGauss s₂ (-y)) H := by
    rw [← residueFourier_const_mul, ← residueFourier_const_mul]
    exact residueFourier_congr_fun _ hloc₂ H
  linear_combination (sexticSymbol s₂ s₁ * sexticSymbol s₁ s₂) *
    (residueFourier (s₂ * A₂) (fun y => sexticSymbol (s₁ * A₁ * y) A₂ *
      sexticGauss s₂ (-(s₁ * A₁ * y))) H * sexticSymbol (s₁ * A₁) s₂ * e₁ +
    sexticSymbol (s₂ * A₂) A₁ * residueFourier (s₁ * A₁)
        (fun x => sexticSymbol x A₁ * sexticGauss s₁ (-x)) H * e₂)

end GaloisForLFunctions.FamilyContinuationTheory
