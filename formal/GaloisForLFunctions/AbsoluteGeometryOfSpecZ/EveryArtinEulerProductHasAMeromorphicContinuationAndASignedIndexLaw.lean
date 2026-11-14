import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheOrdersOfAnArtinLFunctionAreTheNetMultiplicitiesOfItsVirtualConfiguration

/-!
# Artin continuation and its signed Weil index

Brauer induction writes an Artin Euler product as a finite integer product of Hecke
Euler products. Clearing the simple pole of each factor produces analytic functions
`A` and `B` on `Re s > 0`, with `B` nonzero on `Re s > 1` and `A = B L` there.
Thus `A / B` is a meromorphic continuation. Its zero and pole orders are the net
multiplicities of a tempered virtual configuration, whose Weil index counts the
right-half-plane support and the negative multiplicities on the critical line.
-/

noncomputable section
open Complex Set NumberField
open scoped Classical
universe u
namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open HeckeLFunctions HTGeometry IsDedekindDomain Zeta23 ArithmeticCastelnuovoSeveri

/-- Clearing an integer power uses only nonnegative powers in numerator and denominator. -/
private theorem cleared_integer_power (x y : ℂ) (hy : y ≠ 0) (k : ℤ) :
    (x * y) ^ k.toNat * x ^ (-k).toNat =
      ((x * y) ^ (-k).toNat * x ^ k.toNat) * y ^ k := by
  have hp : y ^ k.toNat = y ^ (-k).toNat * y ^ k := by
    rw [← zpow_natCast y k.toNat, ← zpow_natCast y (-k).toNat, ← zpow_add₀ hy]
    congr 1
    omega
  rw [mul_pow, mul_pow, hp]
  ring

/-- A finite integer product of functions with a cleared simple pole has an analytic
numerator and denominator on the right half-plane. -/
theorem exists_analytic_quotient_of_cleared_product {ι : Type*} (n : ι →₀ ℤ)
    (Λ G : ι → ℂ → ℂ)
    (hG : ∀ q, DifferentiableOn ℂ (G q) {s : ℂ | 0 < s.re})
    (hGΛ : ∀ q s, 1 < s.re → G q s = (s - 1) * Λ q s)
    (hΛ : ∀ q s, 1 < s.re → Λ q s ≠ 0) :
    ∃ A B : ℂ → ℂ,
      DifferentiableOn ℂ A {s : ℂ | 0 < s.re} ∧
      DifferentiableOn ℂ B {s : ℂ | 0 < s.re} ∧ (∀ s : ℂ, 1 < s.re → B s ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re → A s = B s * n.prod (fun q k => Λ q s ^ k) := by
  let A := fun s : ℂ => ∏ q ∈ n.support, G q s ^ (n q).toNat * (s - 1) ^ (-(n q)).toNat
  let B := fun s : ℂ => ∏ q ∈ n.support, G q s ^ (-(n q)).toNat * (s - 1) ^ (n q).toNat
  have hx : DifferentiableOn ℂ (fun s : ℂ => s - 1) {s : ℂ | 0 < s.re} :=
    differentiable_id.differentiableOn.sub_const 1
  refine ⟨A, B, DifferentiableOn.fun_finsetProd (fun q _ => (hG q).pow _ |>.mul (hx.pow _)),
    DifferentiableOn.fun_finsetProd (fun q _ => (hG q).pow _ |>.mul (hx.pow _)), ?_, ?_⟩
  · intro s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (fun he => by
      have hre := congrArg Complex.re he
      simp only [Complex.one_re] at hre
      linarith)
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hne : G q s ≠ 0 := by
      rw [hGΛ q s hs]
      exact mul_ne_zero hs1 (hΛ q s hs)
    exact mul_ne_zero (pow_ne_zero _ hne) (pow_ne_zero _ hs1)
  · intro s hs
    dsimp only [A, B, Finsupp.prod]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q hq
    rw [hGΛ q s hs]
    exact cleared_integer_power (s - 1) (Λ q s) (hΛ q s hs) (n q)

variable (K L : Type u) {G V : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Every Artin Euler product admits an analytic numerator and denominator on `Re s > 0`,
with denominator nonzero on `Re s > 1`; no continuation is an input. -/
theorem exists_analytic_quotient_artin (ρ : Representation ℂ G V) :
    ∃ A B : ℂ → ℂ,
      DifferentiableOn ℂ A {s : ℂ | 0 < s.re} ∧
      DifferentiableOn ℂ B {s : ℂ | 0 < s.re} ∧ (∀ s : ℂ, 1 < s.re → B s ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re → A s = B s *
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s := by
  obtain ⟨n, Λ, hΛ, hE⟩ := exists_artinEulerProduct_eq_prod_zpow_heckeL K L ρ
  unfold IsBrauerHeckeEulerProduct at hΛ
  choose c hc ψ hψ using hΛ
  obtain ⟨A, B, hA, hB, hB2, hAB⟩ := exists_analytic_quotient_of_cleared_product n
    (fun q => brauerHeckeEulerProduct K L q (c q) (ψ q))
    (fun q => brauerHeckeCleared K L q (c q) (ψ q))
    (fun q => differentiableOn_brauerHeckeCleared K L q (c q) (ψ q))
    (fun q s hs => brauerHeckeCleared_eq K L q (c q) (ψ q) hs)
    (fun q s hs => brauerHeckeEulerProduct_ne_zero K L q (c q) (ψ q) hs)
  refine ⟨A, B, hA, hB, hB2, fun s hs => ?_⟩
  rw [hAB s hs, hE s hs]
  congr 1
  exact Finsupp.prod_congr fun q _ => by rw [hψ q s]

/-- Every Artin Euler product has a meromorphic continuation to `Re s > 0`. -/
theorem exists_meromorphicContinuation_artin (ρ : Representation ℂ G V) :
    ∃ F : ℂ → ℂ, MeromorphicOn F {s : ℂ | 0 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → F s =
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s := by
  obtain ⟨A, B, hA, hB, hBne, hAB⟩ := exists_analytic_quotient_artin K L ρ
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨fun s => A s / B s, fun s hs => ?_, fun s hs => ?_⟩
  · exact ((hA.analyticOnNhd hU) s hs).meromorphicAt.div
      (((hB.analyticOnNhd hU) s hs).meromorphicAt)
  · apply (div_eq_iff (hBne s hs)).mpr
    exact (hAB s hs).trans (mul_comm _ _)

/-- The Artin product has a continuation whose zero and pole orders equal the net
multiplicities of a tempered virtual configuration, with its exact Weil index law. -/
theorem exists_analytic_quotient_and_virtualConfig_artin (ρ : Representation ℂ G V) :
    ∃ (A B : ℂ → ℂ) (n : brauerElementaryMonomialIndex G →₀ ℤ)
      (Z : brauerElementaryMonomialIndex G → ZeroConfig) (p : ℤ),
      DifferentiableOn ℂ A {s : ℂ | 0 < s.re} ∧
      DifferentiableOn ℂ B {s : ℂ | 0 < s.re} ∧ B 2 ≠ 0 ∧
      (∀ s : ℂ, 1 < s.re → A s = B s *
        numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s) ∧
      (∀ q, SquareRootThreshold.TemperedConfig (Z q)) ∧
      (∀ w : ℂ, 0 < w.re → w ≠ 1 →
        (analyticOrderNatAt A w : ℤ) - analyticOrderNatAt B w = netMult n Z w) ∧
      (analyticOrderNatAt A 1 : ℤ) - analyticOrderNatAt B 1 = -p ∧
      ∀ m : ℕ, (∃ f : Fin m → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
          (∀ i, HasCompactSupport (f i)) ∧
          m ≤ hermNegIndex (n.sum fun q k => (k : ℂ) • zeroGram (Z q) f)) ↔
        (m : ℕ∞) ≤ ({w : ℂ | 1 / 2 < w.re ∧ w ≠ 1 ∧
            analyticOrderNatAt A w ≠ analyticOrderNatAt B w} ∪
          {w : ℂ | w.re = 1 / 2 ∧
            analyticOrderNatAt A w < analyticOrderNatAt B w}).encard := by
  obtain ⟨A, B, hA, hB, hB2, hAB⟩ := exists_analytic_quotient_artin K L ρ
  obtain ⟨n, Z, p, hZ, horders⟩ := exists_virtualConfig_artin K L ρ
  exact ⟨A, B, n, Z, p, hA, hB, hB2 2 (by norm_num), hAB, hZ,
    horders A B hA hB ⟨2, by norm_num, hB2 2 (by norm_num)⟩ hAB⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ

#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.exists_analytic_quotient_artin

#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.exists_meromorphicContinuation_artin

#print axioms GaloisForLFunctions.AbsoluteGeometryOfSpecZ.exists_analytic_quotient_and_virtualConfig_artin
