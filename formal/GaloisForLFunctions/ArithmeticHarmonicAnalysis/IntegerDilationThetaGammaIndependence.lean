import GaloisForLFunctions.ArithmeticHarmonicAnalysis.JacobiThetaGammaCoefficientBoundary
import GaloisForLFunctions.HTGeometry.GammaFieldCoefficientLaw
import GaloisForLFunctions.HTGeometry.ZetaHypertranscendence
import GaloisForLFunctions.HTGeometry.UpperEndDifferentialInstances
import GaloisForLFunctions.HTGeometry.CoordinatewiseDifferentialFamilyMatroid
import GaloisForLFunctions.RHTower.CompletePositiveKolchinFreeRiemannResolution
import GaloisForLFunctions.HTGeometry.AffineFluxTaylorCoeff

/-!
# Integer zeta dilations over the theta–Gamma field

All positive integer dilates of zeta are jointly differentially independent over
`ℂ(s)⟨Γ, θ₂, θ₃, θ₄, E₂⟩`. Gamma asymptotics and simultaneous almost-periodic
recurrence reduce a finite relation to constant coefficients. Analytic continuation
and explicit rotation of jets then connect the physical functions to the independent
arithmetic dilation family. Integer differential–Mahler equations in this coefficient
field are excluded as a consequence.
-/

open Complex Filter Set Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry RHTower
open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaJoint

local instance : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
local instance : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
local instance : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- A common coefficient-ratio limit preserves every finite almost-periodic relation. -/
theorem line_relation_of_ratios {N : ℕ} (σ : ℝ)
    (F M : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hc : ∀ α, Continuous (fun t : ℝ => M α ((σ : ℂ) + t * I)))
    (hap : ∀ α, _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => M α ((σ : ℂ) + t * I)))
    (hcoeff : ∀ α, Tendsto
      (fun t : ℝ => F α ((σ : ℂ) + t * I) / F β ((σ : ℂ) + t * I))
      atTop (𝓝 (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + t * I) ≠ 0)
    (hrel : ∀ᶠ t : ℝ in atTop, ∑ α, F α ((σ : ℂ) + t * I) * M α ((σ : ℂ) + t * I) = 0)
    (t₀ : ℝ) : ∑ α, d α * M α ((σ : ℂ) + t₀ * I) = 0 := by
  let s₀ : ℂ := σ + t₀ * I
  have hs (t : ℝ) : s₀ + t * I = (σ : ℂ) + ((t + t₀ : ℝ) : ℂ) * I := by
    dsimp only [s₀]
    push_cast
    ring
  have hshift : Tendsto (fun t : ℝ => t + t₀) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hc' : ∀ α, Continuous (fun t : ℝ => M α (s₀ + t * I)) := by
    intro α
    simp only [hs]
    exact (hc α).comp (continuous_id.add continuous_const)
  have hap' : ∀ α, _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => M α (s₀ + t * I)) := by
    intro α
    simp only [hs]
    exact isBohrAlmostPeriodic_comp_add_const (hap α) t₀
  have hcoeff' : ∀ α, Tendsto
      (fun t : ℝ => F α (s₀ + t * I) / F β (s₀ + t * I)) atTop (𝓝 (d α)) := by
    intro α
    simp only [hs]
    exact (hcoeff α).comp hshift
  have hFβ' : ∀ᶠ t : ℝ in atTop, F β (s₀ + t * I) ≠ 0 := by
    simpa only [hs] using hshift.eventually hFβ
  have hrel' : ∀ᶠ t : ℝ in atTop, ∑ α, F α (s₀ + t * I) * M α (s₀ + t * I) = 0 := by
    simpa only [hs] using hshift.eventually hrel
  exact (recurrence_collapse_of_bohr_return_eventual F M β s₀ d
    hrel' hc' hap' hFβ' hcoeff').1

private theorem analytic_relation_on_line {N : ℕ} (σ : ℝ)
    (W Ψ : Fin N → upperEndAnalyticSubring) (F M : Fin N → ℂ → ℂ)
    (hW : ∀ α, upperEndAnalyticSubring.subtype (W α) = Germ.coeRingHom upperEndFilter (F α))
    (hΨ : ∀ α, upperEndAnalyticSubring.subtype (Ψ α) = Germ.coeRingHom upperEndFilter (M α))
    (hrel : ∑ α, W α * Ψ α = 0) :
    ∀ᶠ t : ℝ in atTop, ∑ α, F α ((σ : ℂ) + t * I) * M α ((σ : ℂ) + t * I) = 0 := by
  have h := congrArg upperEndAnalyticSubring.subtype hrel
  simp only [map_sum, map_mul, map_zero, hW, hΨ] at h
  have heq : Germ.coeRingHom upperEndFilter
      (fun z : ℂ => ∑ α, F α z * M α z) = 0 := by
    have he : (fun z : ℂ => ∑ α, F α z * M α z) = ∑ α, F α * M α := by
      ext z
      simp only [Finset.sum_apply, Pi.mul_apply]
    rw [he, map_sum]
    simpa only [map_mul] using h
  have hg : (fun z : ℂ => ∑ α, F α z * M α z) =ᶠ[upperEndFilter] (0 : ℂ → ℂ) := by
    apply Germ.coe_eq.mp
    exact heq.trans (map_zero (Germ.coeRingHom upperEndFilter)).symm
  exact eventually_line_of_upperEnd hg σ

/-- Gamma jet-algebra coefficients collapse to constants for an arbitrary finite
family of actual almost-periodic analytic germs. -/
theorem gammaAlgebra_relation_collapse {N : ℕ} (hN : 0 < N) {σ : ℝ} (hσ : 0 < σ)
    (W Ψ : Fin N → upperEndAnalyticSubring) (F M : Fin N → ℂ → ℂ)
    (hW : ∀ α, upperEndAnalyticSubring.subtype (W α) = Germ.coeRingHom upperEndFilter (F α))
    (hΨ : ∀ α, upperEndAnalyticSubring.subtype (Ψ α) = Germ.coeRingHom upperEndFilter (M α))
    (hWmem : ∀ α, algebraMap upperEndAnalyticSubring upperEndMeroField (W α) ∈
      differentialJetAlgebra (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hW0 : ∀ α, W α ≠ 0)
    (hc : ∀ α, Continuous (fun t : ℝ => M α ((σ : ℂ) + t * I)))
    (hap : ∀ α, _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => M α ((σ : ℂ) + t * I)))
    (hrel : ∑ α, W α * Ψ α = 0) :
    ∃ (β : Fin N) (d : Fin N → ℂ), d β = 1 ∧
      ∀ t : ℝ, ∑ α, d α * M α ((σ : ℂ) + t * I) = 0 := by
  have hdat : ∀ α, ∃ (u a d b : ℕ) (c : ℂ), c ≠ 0 ∧
      Tendsto (fun t : ℝ => F α ((σ : ℂ) + t * I) / gammaJetShape σ u a d b t)
        atTop (𝓝 c) := by
    intro α
    have hx0 : algebraMap upperEndAnalyticSubring upperEndMeroField (W α) ≠ 0 :=
      fun he => hW0 α ((IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField)
        (he.trans (map_zero _).symm))
    obtain ⟨q, V, G, u, a, d, b, c, hq, hc0, hV, hG, hlim⟩ :=
      exists_gammaAlgebra_line_datum hσ (hWmem α) hx0
    refine ⟨u, a, d, b, c, hc0, hlim.congr' ?_⟩
    have heq := eventually_line_eq_of_representatives σ hq (by simp : (1 : Polynomial ℂ) ≠ 0)
      hV (by simp : upperEndPolyToMero (1 : Polynomial ℂ) *
        algebraMap upperEndAnalyticSubring upperEndMeroField (W α) =
        algebraMap upperEndAnalyticSubring upperEndMeroField (W α)) hG (hW α)
    filter_upwards [heq] with t ht
    simpa only [Polynomial.eval_one, div_one] using congrArg (fun z : ℂ => z / gammaJetShape σ u a d b t) ht
  choose u a d b c hc0 hlim using hdat
  obtain ⟨β, r, hr, hrβ⟩ := exists_dominant_with_shape_ratios hσ hN u a d b
  obtain ⟨hFβ, -, hcoeff⟩ := tendsto_family_ratio_of_normalized
    (F := fun α t => F α ((σ : ℂ) + t * I))
    (shape := fun α => gammaJetShape σ (u α) (a α) (d α) (b α))
    (c := c) (r := r) β (hc0 β)
    (fun α => eventually_gammaJetShape_ne_zero hσ (u α) (a α) (d α) (b α)) hlim hr
  refine ⟨β, fun α => c α * r α / c β, self_ratio_eq_one β (hc0 β) hrβ, ?_⟩
  exact fun t => line_relation_of_ratios σ F M _ β hc hap hcoeff hFβ
    (analytic_relation_on_line σ W Ψ F M hW hΨ hrel) t

/-- A finite relation over the actual Gamma differential field among almost-periodic
analytic germs yields a nonzero constant-coefficient relation on the line. -/
theorem gammaField_relation_collapse {N : ℕ} (hN : 0 < N) {σ : ℝ} (hσ : 0 < σ)
    (Ψ : Fin N → upperEndAnalyticSubring) (M : Fin N → ℂ → ℂ)
    (hΨ : ∀ α, upperEndAnalyticSubring.subtype (Ψ α) = Germ.coeRingHom upperEndFilter (M α))
    (x : Fin N → upperEndMeroField) (hx : ∀ α, x α ∈ gammaCoefficientField)
    (hx0 : ∀ α, x α ≠ 0)
    (hc : ∀ α, Continuous (fun t : ℝ => M α ((σ : ℂ) + t * I)))
    (hap : ∀ α, _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => M α ((σ : ℂ) + t * I)))
    (hrel : ∑ α, x α * algebraMap upperEndAnalyticSubring upperEndMeroField (Ψ α) = 0) :
    ∃ (β : Fin N) (d : Fin N → ℂ), d β = 1 ∧
      ∀ t : ℝ, ∑ α, d α * M α ((σ : ℂ) + t * I) = 0 := by
  classical
  -- Clear the field denominator, then the rational-function denominators.
  obtain ⟨D, hD0, hDmem⟩ := exists_common_denominator (F := RatFunc ℂ) x hx
  have hy0 : ∀ α, x α * D ≠ 0 := fun α => mul_ne_zero (hx0 α) hD0
  choose q W G u a d b r hq hr hW hG hlim using
    fun α => exists_gammaAlgebra_datum hσ (hDmem α) (hy0 α)
  let Qc : Fin N → Polynomial ℂ := fun α => ∏ γ ∈ Finset.univ.erase α, q γ
  let V : Fin N → upperEndAnalyticSubring := fun α => upperEndPolyToAnalytic (Qc α) * W α
  have hQ0 : (∏ γ : Fin N, q γ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun γ _ => hq γ)
  have hQmero : upperEndPolyToMero (∏ γ : Fin N, q γ) ≠ 0 := fun he =>
    hQ0 (upperEndPolyToMero_injective (by rw [he, map_zero]))
  have hVimg (α : Fin N) : algebraMap upperEndAnalyticSubring upperEndMeroField (V α) =
      upperEndPolyToMero (∏ γ : Fin N, q γ) * (x α * D) := by
    rw [show V α = upperEndPolyToAnalytic (Qc α) * W α from rfl, map_mul, ← hW α]
    have hsplit : (∏ γ : Fin N, q γ) = q α * Qc α :=
      (Finset.mul_prod_erase Finset.univ q (Finset.mem_univ α)).symm
    rw [hsplit, map_mul]
    change upperEndPolyToMero (Qc α) * (upperEndPolyToMero (q α) * (x α * D)) =
      upperEndPolyToMero (q α) * upperEndPolyToMero (Qc α) * (x α * D)
    ring
  have hVmem : ∀ α, algebraMap upperEndAnalyticSubring upperEndMeroField (V α) ∈
      differentialJetAlgebra (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField) := by
    intro α
    rw [hVimg]
    refine mul_mem ?_ (hDmem α)
    rw [← upperEndRatfuncToMero_algebraMap_polynomial]
    exact Subalgebra.algebraMap_mem _ _
  have hV0 : ∀ α, V α ≠ 0 := by
    intro α he
    have hi := hVimg α
    rw [he, map_zero] at hi
    exact (mul_ne_zero hQmero (hy0 α)) hi.symm
  have hcarrier : ∑ α, V α * Ψ α = 0 := by
    apply IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
    rw [map_sum, map_zero]
    have heq : ∀ α, algebraMap upperEndAnalyticSubring upperEndMeroField (V α * Ψ α) =
        (upperEndPolyToMero (∏ γ : Fin N, q γ) * D) *
          (x α * algebraMap upperEndAnalyticSubring upperEndMeroField (Ψ α)) := by
      intro α
      rw [map_mul, hVimg]
      ring
    rw [Finset.sum_congr rfl (fun α _ => heq α), ← Finset.mul_sum, hrel, mul_zero]
  refine gammaAlgebra_relation_collapse hN hσ V Ψ (fun α z => (Qc α).eval z * G α z)
    M ?_ hΨ hVmem hV0 hc hap hcarrier
  intro α
  rw [show V α = upperEndPolyToAnalytic (Qc α) * W α from rfl,
    map_mul, polyToAnalytic_subtype, hG α, ← map_mul]
  rfl

/-- An algebraically independent almost-periodic family on a physical vertical
line remains independent over the actual Gamma differential field. -/
theorem algebraicIndependent_gamma_of_line {J : Type*} {σ : ℝ} (hσ : 0 < σ)
    (Ψ : J → upperEndAnalyticSubring) (F : J → ℂ → ℂ)
    (hΨ : ∀ j, upperEndAnalyticSubring.subtype (Ψ j) = Germ.coeRingHom upperEndFilter (F j))
    (hc : ∀ j, Continuous (fun t : ℝ => F j ((σ : ℂ) + t * I)))
    (hap : ∀ j, _root_.HTGeometry.IsBohrAlmostPeriodic (fun t : ℝ => F j ((σ : ℂ) + t * I)))
    (hai : AlgebraicIndependent ℂ (fun j (t : ℝ) => F j ((σ : ℂ) + t * I))) :
    AlgebraicIndependent ↥gammaCoefficientField
      (fun j => algebraMap upperEndAnalyticSubring upperEndMeroField (Ψ j)) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  -- Enumerate only the nonzero coefficients, preserving distinct monomials.
  let N := P.support.card
  let e : Fin N → J →₀ ℕ := fun α => (P.support.equivFin.symm α).1
  let c : Fin N → ↥gammaCoefficientField := fun α => P.coeff (e α)
  have hN : 0 < N := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr (fun h => hP0 (MvPolynomial.support_eq_empty.mp h)))
  have hei : Function.Injective e := fun α β h =>
    P.support.equivFin.symm.injective (Subtype.ext h)
  have hc0 : ∀ α, c α ≠ 0 := fun α =>
    MvPolynomial.mem_support_iff.mp (P.support.equivFin.symm α).2
  let Ξ : Fin N → upperEndAnalyticSubring := fun α => (e α).prod fun j k => Ψ j ^ k
  let M : Fin N → ℂ → ℂ := fun α z => (e α).prod fun j k => F j z ^ k
  have hΞ : ∀ α, upperEndAnalyticSubring.subtype (Ξ α) = Germ.coeRingHom upperEndFilter (M α) := by
    intro α
    dsimp only [Ξ, M, Finsupp.prod]
    rw [map_prod]
    simp_rw [map_pow, hΨ, ← map_pow]
    rw [← map_prod]
    congr 1
    ext z
    simp only [Finset.prod_apply, Pi.pow_apply]
  have hmap (α : Fin N) : algebraMap upperEndAnalyticSubring upperEndMeroField (Ξ α) =
      (e α).prod fun j k => (algebraMap upperEndAnalyticSubring upperEndMeroField (Ψ j)) ^ k := by
    simp only [Ξ, Finsupp.prod, map_prod, map_pow]
  have hrel : ∑ α, (c α : upperEndMeroField) *
      algebraMap upperEndAnalyticSubring upperEndMeroField (Ξ α) = 0 := by
    simp_rw [hmap]
    calc
      _ = ∑ m ∈ P.support, ((P.coeff m : ↥gammaCoefficientField) : upperEndMeroField) *
          m.prod (fun j k => (algebraMap upperEndAnalyticSubring upperEndMeroField (Ψ j)) ^ k) := by
        rw [← Finset.sum_attach P.support]
        exact Fintype.sum_equiv P.support.equivFin.symm _ _ (fun _ => rfl)
      _ = MvPolynomial.aeval
          (fun j => algebraMap upperEndAnalyticSubring upperEndMeroField (Ψ j)) P := by
        rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
        rfl
      _ = 0 := hP
  have hMc : ∀ α, Continuous (fun t : ℝ => M α ((σ : ℂ) + t * I)) := by
    intro α
    exact continuous_finsetProd _ fun j _ => (hc j).pow (e α j)
  have hMa : ∀ α, _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => M α ((σ : ℂ) + t * I)) := by
    intro α
    exact isBohrAlmostPeriodic_finsetProd (e α).support _
      (fun j => (hc j).pow (e α j))
      (fun j => isBohrAlmostPeriodic_pow (hc j) (hap j) (e α j))
  obtain ⟨β, d, hdβ, hd⟩ := gammaField_relation_collapse hN hσ Ξ M hΞ
    (fun α => (c α : upperEndMeroField)) (fun α => (c α).2)
    (fun α h => hc0 α (Subtype.ext h)) hMc hMa hrel
  let Q : MvPolynomial J ℂ := ∑ α, MvPolynomial.monomial (e α) (d α)
  have hQ : Q = 0 := by
    apply hai.eq_zero_of_aeval_eq_zero
    ext t
    simp only [Q, map_sum, MvPolynomial.aeval_monomial, Finsupp.prod,
      Finset.sum_apply, Finset.prod_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.algebraMap_apply]
    change (∑ α, d α * M α ((σ : ℂ) + t * I)) = 0
    exact hd t
  have hcoeff : Q.coeff (e β) = d β := by
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single β]
    · simp
    · intro α _ hα
      exact if_neg (fun h => hα (hei h))
    · simp
  rw [hQ, MvPolynomial.coeff_zero, hdβ] at hcoeff
  exact zero_ne_one hcoeff

private theorem differentialAlgebraicOver_of_mem_adjoin
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (y : E) {x : E} (hx : x ∈ differentialAdjoin F ({y} : Set E)) :
    DifferentialAlgebraicOver (differentialAdjoin F ({y} : Set E)) x := by
  let S := differentialAdjoin F ({y} : Set E)
  letI : DifferentialAlgebra S E :=
    ⟨fun c => derivationClosedDifferential_apply S
      (derivationClosed_differentialAdjoin F {y}) c⟩
  exact differentialAlgebraicOver_algebraMap (F := S) (E := E) (⟨x, hx⟩ : S)

/-- Inverting all coordinates except the first converts the signed Möbius family
into the positive integer zeta dilates. -/
def rotatedZetaMero (n : ℕ) : upperEndMeroField :=
  if n = 0 then zetaNegativeDilatedMoebiusUpperEndCarrier (n + 1)
  else -(zetaNegativeDilatedMoebiusUpperEndCarrier (n + 1))⁻¹

theorem rotatedZetaMero_differentialIndependent :
    DifferentialIndependent upperEndRationalCoordinateField rotatedZetaMero := by
  let x : ℕ → upperEndMeroField := fun n =>
    zetaNegativeDilatedMoebiusUpperEndCarrier (n + 1)
  have hx : DifferentialIndependent upperEndRationalCoordinateField x :=
    zetaNegativeDilatedMoebiusUpperEndCarrier_differentialIndependent_of_injective
      (fun n => n + 1) (fun n => Nat.succ_pos n) (fun _ _ h => Nat.add_right_cancel h)
  apply (coordinatewiseMutuallyDifferentialAlgebraic_iff x rotatedZetaMero ?_ ?_).mp hx
  · intro n
    apply differentialAlgebraicOver_of_mem_adjoin
    have hy : rotatedZetaMero n ∈ differentialAdjoin upperEndRationalCoordinateField
        ({rotatedZetaMero n} : Set upperEndMeroField) := subset_differentialAdjoin upperEndRationalCoordinateField
      ({rotatedZetaMero n} : Set upperEndMeroField) (mem_singleton _)
    by_cases hn : n = 0
    · simpa only [rotatedZetaMero, if_pos hn, x] using hy
    · have hi := (differentialAdjoin upperEndRationalCoordinateField
        ({rotatedZetaMero n} : Set upperEndMeroField)).neg_mem
        ((differentialAdjoin upperEndRationalCoordinateField
          ({rotatedZetaMero n} : Set upperEndMeroField)).inv_mem hy)
      simpa only [rotatedZetaMero, if_neg hn, inv_neg, inv_inv, neg_neg, x] using hi
  · intro n
    apply differentialAlgebraicOver_of_mem_adjoin
    have hxmem : x n ∈ differentialAdjoin upperEndRationalCoordinateField
        ({x n} : Set upperEndMeroField) := subset_differentialAdjoin upperEndRationalCoordinateField
      ({x n} : Set upperEndMeroField) (mem_singleton _)
    by_cases hn : n = 0
    · simpa only [rotatedZetaMero, if_pos hn, x] using hxmem
    · rw [rotatedZetaMero, if_neg hn]
      exact (differentialAdjoin upperEndRationalCoordinateField ({x n} : Set upperEndMeroField)).neg_mem
        ((differentialAdjoin upperEndRationalCoordinateField ({x n} : Set upperEndMeroField)).inv_mem hxmem)

/-- The actual positive integer dilates in the physical Dirichlet variable. -/
def zetaDilation (n : ℕ) (s : ℂ) : ℂ := riemannZeta ((n + 1 : ℕ) * s)

theorem zetaDilation_analytic_upper (n : ℕ) :
    AnalyticOnNhd ℂ (zetaDilation n) (upperTail 0) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_upperTail 0)
  intro z hz
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hi : 0 < (((n + 1 : ℕ) : ℂ) * z).im := by
    simpa only [mul_im, natCast_re, natCast_im, zero_mul, add_zero] using mul_pos hpos hz
  have hne : ((n + 1 : ℕ) : ℂ) * z ≠ 1 := by
    intro he
    rw [he] at hi
    norm_num at hi
  exact ((differentiableAt_riemannZeta hne).comp z
    (differentiableAt_id.const_mul _)).differentiableWithinAt

/-- The rotated representatives are analytic where the Dirichlet series converge. -/
theorem zetaDilation_rotated_analytic (n : ℕ) :
    AnalyticOnNhd ℂ (fun z => zetaDilation n (-I * z)) (upperTail 1) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_upperTail 1)
  intro z hz
  have h1 : (1 : ℝ) < (-I * z).re := by simpa [mul_re, upperTail] using hz
  have hgt : 1 < (((n + 1 : ℕ) : ℂ) * (-I * z)).re :=
    one_lt_natCast_mul_re (Nat.succ_ne_zero n)
      (one_div_natCast_lt_re (Nat.succ_ne_zero n) h1)
  have hne : ((n + 1 : ℕ) : ℂ) * (-I * z) ≠ 1 := by
    intro he
    rw [he] at hgt
    norm_num at hgt
  exact ((differentiableAt_riemannZeta hne).comp z
    ((differentiableAt_id.const_mul (-I)).const_mul _)).differentiableWithinAt

def zetaDilationAnalytic (n : ℕ) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (zetaDilation n),
    ⟨zetaDilation n, 0, zetaDilation_analytic_upper n, rfl⟩⟩

def rotatedZetaAnalytic (n : ℕ) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (fun z => zetaDilation n (-I * z)),
    ⟨_, 1, zetaDilation_rotated_analytic n, rfl⟩⟩

/-- Positive real changes of speed preserve relative density of almost periods. -/
theorem bohr_comp_pos_mul {f : ℝ → ℂ} (hf : _root_.HTGeometry.IsBohrAlmostPeriodic f)
    {c : ℝ} (hc : 0 < c) :
    _root_.HTGeometry.IsBohrAlmostPeriodic (fun t => f (c * t)) := by
  intro ε hε
  obtain ⟨L, hL, hperiod⟩ := hf ε hε
  refine ⟨L / c, div_pos hL hc, fun a => ?_⟩
  obtain ⟨τ, hτ, hb⟩ := hperiod (c * a)
  refine ⟨τ / c, ⟨?_, ?_⟩, fun x => ?_⟩
  · exact (le_div_iff₀ hc).mpr (by nlinarith [hτ.1])
  · apply (div_le_iff₀ hc).mpr
    calc τ ≤ c * a + L := hτ.2
      _ = (a + L / c) * c := by field_simp
  · have he : c * (x + τ / c) = c * x + τ := by field_simp
    dsimp only
    rw [he]
    exact hb (c * x)

/-- Every jet of every positive integer zeta dilation is almost periodic on `Re s=2`. -/
theorem zetaDilation_jet_line (n k : ℕ) :
    Continuous (fun t : ℝ => iteratedDeriv k (zetaDilation n) (2 + t * I)) ∧
    _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => iteratedDeriv k (zetaDilation n) (2 + t * I)) := by
  let c : ℝ := (n + 1 : ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : 1 ≤ c := by dsimp [c]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hσ : 1 < c * 2 := by linarith
  have hRσ : (1 : ℝ) ≤ c * 2 - 1 := by linarith
  have hj := isStripAlmostPeriodic_iteratedDeriv
    (differentiableOn_zeta_verticalStrip hσ hRσ) (isStripAlmostPeriodic_zeta hRσ) k
  have hjc := continuous_line_restriction (by norm_num : (0 : ℝ) < 1) hj.1
  have hja := isBohrAlmostPeriodic_line (by norm_num : (0 : ℝ) < 1) hj.2
  have hfun : (fun t : ℝ => iteratedDeriv k (zetaDilation n) (2 + t * I)) =
      (fun t : ℝ => (c : ℂ)^k * iteratedDeriv k riemannZeta
        (((c * 2 : ℝ) : ℂ) + ((c * t : ℝ) : ℂ) * I)) := by
    funext t
    change iteratedDeriv k (fun z => riemannZeta (((n + 1 : ℕ) : ℂ) * z)) _ = _
    rw [iteratedDeriv_comp_const_mul_of_ne _ _ (by exact_mod_cast Nat.succ_ne_zero n)]
    congr 1
    congr 1
    dsimp only [c]
    push_cast
    ring
  rw [hfun]
  exact ⟨continuous_const.mul (hjc.comp (continuous_const.mul continuous_id)),
    isBohrAlmostPeriodic_const_mul _ (bohr_comp_pos_mul hja hc)⟩

/-- All mixed jet monomials have the recurrence needed for Gamma coefficient collapse. -/
theorem zetaDilation_monomial_line (e : (ℕ × ℕ) →₀ ℕ) :
    Continuous (fun t : ℝ => e.prod fun p a =>
      (iteratedDeriv p.2 (zetaDilation p.1) (2 + t * I)) ^ a) ∧
    _root_.HTGeometry.IsBohrAlmostPeriodic (fun t : ℝ => e.prod fun p a =>
      (iteratedDeriv p.2 (zetaDilation p.1) (2 + t * I)) ^ a) := by
  constructor
  · exact continuous_finsetProd _ fun p _ => (zetaDilation_jet_line p.1 p.2).1.pow (e p)
  · exact isBohrAlmostPeriodic_finsetProd e.support _
      (fun p => (zetaDilation_jet_line p.1 p.2).1.pow (e p))
      (fun p => isBohrAlmostPeriodic_pow (zetaDilation_jet_line p.1 p.2).1
        (zetaDilation_jet_line p.1 p.2).2 (e p))

/-- The rotated analytic germ is the inverse of the dilated Möbius germ. -/
theorem moebius_mul_rotatedZeta (n : ℕ) :
    dilatedMoebiusUpperEndCarrier (n + 1) *
      algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedZetaAnalytic n) = 1 := by
  let A := finiteAbscissaLSeriesUpperEndAnalyticElement
    (dilatedMoebiusFiniteAbscissaSource (n + 1))
  have ha : A * rotatedZetaAnalytic n = 1 := by
    apply Subtype.ext
    change (Germ.coeRingHom upperEndFilter
        (fun z : ℂ => LSeries
          (fun k => (dilatedMoebiusFiniteAbscissaSource (n + 1)).1 k) (-I * z))) *
      (Germ.coeRingHom upperEndFilter (fun z => zetaDilation n (-I * z))) = 1
    rw [← map_mul, ← map_one (Germ.coeRingHom upperEndFilter)]
    apply Germ.coe_eq.mpr
    change ∀ᶠ z : ℂ in upperEndFilter, LSeries
      (fun k => (dilatedMoebiusFiniteAbscissaSource (n + 1)).1 k) (-I * z) *
      zetaDilation n (-I * z) = 1
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨1, trivial, fun z hz => ?_⟩
    have h1 : 1 < (-I * z).re := by simpa [mul_re, upperTail] using hz
    have hsm := one_div_natCast_lt_re (Nat.succ_ne_zero n) h1
    have hgt := one_lt_natCast_mul_re (Nat.succ_ne_zero n) hsm
    change LSeries (fun k => (dilatedMoebiusFiniteAbscissaSource (n + 1)).1 k)
      (-I * z) * riemannZeta (((n + 1 : ℕ) : ℂ) * (-I * z)) = 1
    rw [dilatedMoebiusFiniteAbscissaSource_val (Nat.succ_ne_zero n)]
    have heq : (fun k => mPart (n + 1)
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) k) =
        (fun k => ((mPart (n + 1) (ArithmeticFunction.moebius : ArithmeticFunction ℤ) k : ℤ) : ℂ)) := by
      funext k
      rw [← mPart_intCoe]
      rfl
    rw [heq, LSeries_mPart_moebius (Nat.succ_ne_zero n) hsm]
    exact inv_mul_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hgt)
  rw [dilatedMoebiusUpperEndCarrier_eq_source]
  change algebraMap upperEndAnalyticSubring upperEndMeroField A *
    algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedZetaAnalytic n) = 1
  rw [← map_mul, ha, map_one]

/-- Explicit identification with actual rotated zeta, including the exceptional first coordinate. -/
theorem rotatedZetaMero_eq_analytic (n : ℕ) :
    rotatedZetaMero n =
      algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedZetaAnalytic n) := by
  by_cases hn : n = 0
  · subst n
    rw [rotatedZetaMero, if_pos rfl]
    change algebraMap upperEndAnalyticSubring upperEndMeroField
        (finiteAbscissaLSeriesUpperEndAnalyticElement zetaSource) =
      algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedZetaAnalytic 0)
    apply congrArg (algebraMap upperEndAnalyticSubring upperEndMeroField)
    apply Subtype.ext
    change (finiteAbscissaLSeriesToUpperEndGerm zetaSource : Germ upperEndFilter ℂ) = _
    rw [zetaUpperEndGerm_eq]
    change ((fun z => riemannZeta (-I * z)) : Germ upperEndFilter ℂ) =
      ((fun z => zetaDilation 0 (-I * z)) : Germ upperEndFilter ℂ)
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by simp [zetaDilation]
  · have hn1 : n + 1 ≠ 1 := by omega
    have hm := moebius_mul_rotatedZeta n
    have he : algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedZetaAnalytic n) =
        (dilatedMoebiusUpperEndCarrier (n + 1))⁻¹ := eq_inv_of_mul_eq_one_left (by rwa [mul_comm])
    rw [he, rotatedZetaMero, if_neg hn,
      zetaNegativeDilatedMoebiusUpperEndCarrier_eq_negative hn1,
      dilatedMoebiusUpperEndCarrier, inv_neg]

/-- A constant relation on the physical vertical line continues to the right
half-plane and hence vanishes as a rotated upper-end germ. -/
theorem rotated_germ_zero_of_line {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 1 < z.re})
    (hline : ∀ t : ℝ, f (2 + t * I) = 0) :
    Germ.coeRingHom upperEndFilter (fun z => f (-I * z)) = 0 := by
  have hsub : verticalStrip 2 (1 / 2) ⊆ {z : ℂ | 1 < z.re} := by
    intro z hz
    have hh := (abs_lt.mp (show |z.re - 2| < 1 / 2 from hz)).1
    dsimp only [mem_setOf_eq]
    linarith
  have hs : EqOn f (fun _ => 0) (verticalStrip 2 (1 / 2)) :=
    eqOn_of_eqOn_line (by norm_num : (0 : ℝ) < 1 / 2)
      (hf.differentiableOn.mono hsub) (differentiableOn_const _) hline
  have h2 : (2 : ℂ) ∈ verticalStrip 2 (1 / 2) := by
    change |(2 : ℂ).re - 2| < 1 / 2
    norm_num
  have he : f =ᶠ[𝓝 (2 : ℂ)] (fun _ => 0) :=
    Filter.eventuallyEq_of_mem ((isOpen_verticalStrip 2 (1 / 2)).mem_nhds h2) hs
  have hglobal : EqOn f (fun _ => 0) {z : ℂ | 1 < z.re} :=
    hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_halfSpace_re_gt 1).isPreconnected (by norm_num) he
  rw [← map_zero (Germ.coeRingHom upperEndFilter)]
  apply Germ.coe_eq.mpr
  change ∀ᶠ z : ℂ in upperEndFilter, f (-I * z) = 0
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨1, trivial, fun z hz => hglobal ?_⟩
  simpa only [mem_setOf_eq, mul_re, neg_re, I_re, neg_im, I_im,
    neg_zero, zero_mul, neg_mul, one_mul, zero_sub, neg_neg, upperTail] using hz

/-- Physical zeta dilates and all their jets are analytic on the common
half-plane of absolute convergence. -/
theorem zetaDilation_analytic_right (n : ℕ) :
    AnalyticOnNhd ℂ (zetaDilation n) {z : ℂ | 1 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const continuous_re)
  intro z hz
  have hgt := one_lt_natCast_mul_re (Nat.succ_ne_zero n)
    (one_div_natCast_lt_re (Nat.succ_ne_zero n) hz)
  have hne : ((n + 1 : ℕ) : ℂ) * z ≠ 1 := by
    intro he
    rw [he] at hgt
    norm_num at hgt
  exact ((differentiableAt_riemannZeta hne).comp z
    (differentiableAt_id.const_mul _)).differentiableWithinAt

private def complexAnalytic : ℂ →+* upperEndAnalyticSubring :=
  upperEndPolyToAnalytic.comp Polynomial.C

private theorem complexAnalytic_repr (c : ℂ) :
    upperEndAnalyticSubring.subtype (complexAnalytic c) =
      Germ.coeRingHom upperEndFilter (fun _ : ℂ => c) := by
  rw [complexAnalytic, RingHom.comp_apply, polyToAnalytic_subtype]
  congr 1
  ext z
  exact Polynomial.eval_C

private theorem polynomial_analytic_repr {J : Type*}
    (Ψ : J → upperEndAnalyticSubring) (F : J → ℂ → ℂ)
    (hΨ : ∀ j, upperEndAnalyticSubring.subtype (Ψ j) = Germ.coeRingHom upperEndFilter (F j))
    (Q : MvPolynomial J ℂ) :
    upperEndAnalyticSubring.subtype (MvPolynomial.eval₂ complexAnalytic Ψ Q) =
      Germ.coeRingHom upperEndFilter (fun z => MvPolynomial.eval (fun j => F j z) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.eval₂_C, complexAnalytic_repr]
      congr 1
      ext z
      simp
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add, map_add, hP, hQ, ← map_add]
      congr 1
      ext z
      simp
  | mul_X P j hP =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, hP, hΨ j, ← map_mul]
      congr 1
      ext z
      simp

private theorem analyticOnNhd_polynomial_family {J : Type*} (F : J → ℂ → ℂ)
    {U : Set ℂ} (hF : ∀ j, AnalyticOnNhd ℂ (F j) U) (Q : MvPolynomial J ℂ) :
    AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (fun j => F j z) Q) U := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.eval_C]
      exact analyticOnNhd_const
  | add P Q hP hQ =>
      simp only [MvPolynomial.eval_add]
      exact hP.add hQ
  | mul_X P j hP =>
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      exact hP.mul (hF j)

/-- Algebraic independence of explicitly rotated analytic representatives
implies independence of the physical vertical-line restrictions. -/
theorem algebraicIndependent_line_of_rotated {J : Type*}
    (F : J → ℂ → ℂ) (Ψ : J → upperEndAnalyticSubring)
    (hF : ∀ j, AnalyticOnNhd ℂ (F j) {z : ℂ | 1 < z.re})
    (hΨ : ∀ j, upperEndAnalyticSubring.subtype (Ψ j) =
      Germ.coeRingHom upperEndFilter (fun z => F j (-I * z)))
    (hai : AlgebraicIndependent ℂ
      (fun j => algebraMap upperEndAnalyticSubring upperEndMeroField (Ψ j))) :
    AlgebraicIndependent ℂ (fun j (t : ℝ) => F j (2 + t * I)) := by
  rw [algebraicIndependent_iff]
  intro Q hQ
  have hline : ∀ t : ℝ, MvPolynomial.eval (fun j => F j (2 + t * I)) Q = 0 := by
    intro t
    have hp : ∀ P : MvPolynomial J ℂ,
        (MvPolynomial.aeval (fun j (t : ℝ) => F j (2 + t * I)) P) t =
          MvPolynomial.eval (fun j => F j (2 + t * I)) P := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C c => simp
      | add P R hP hR => simp [hP, hR]
      | mul_X P j hP => simp [hP]
    rw [← hp Q, hQ]
    rfl
  have hzero := rotated_germ_zero_of_line (analyticOnNhd_polynomial_family F hF Q) hline
  have ha : MvPolynomial.eval₂ complexAnalytic Ψ Q = 0 := by
    apply Subtype.ext
    rw [show ((MvPolynomial.eval₂ complexAnalytic Ψ Q : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) = Germ.coeRingHom upperEndFilter
          (fun z => MvPolynomial.eval (fun j => F j (-I * z)) Q) from
      polynomial_analytic_repr Ψ (fun j z => F j (-I * z)) hΨ Q]
    exact hzero
  apply hai.eq_zero_of_aeval_eq_zero
  have hm := congrArg (algebraMap upperEndAnalyticSubring upperEndMeroField) ha
  rw [map_zero, MvPolynomial.hom_eval₂] at hm
  exact hm

/-- The rotated representative of a physical jet includes the inverse chain factor. -/
def rotatedPhysicalJet (p : ℕ × ℕ) : upperEndAnalyticSubring :=
  complexAnalytic (((-I) ^ p.2)⁻¹) *
    (upperEndAnalyticDeriv^[p.2]) (rotatedZetaAnalytic p.1)

theorem rotatedPhysicalJet_repr (p : ℕ × ℕ) :
    upperEndAnalyticSubring.subtype (rotatedPhysicalJet p) =
      Germ.coeRingHom upperEndFilter
        (fun z => iteratedDeriv p.2 (zetaDilation p.1) (-I * z)) := by
  have hr : upperEndAnalyticSubring.subtype
      ((upperEndAnalyticDeriv^[p.2]) (rotatedZetaAnalytic p.1)) =
      Germ.coeRingHom upperEndFilter (iteratedDeriv p.2 (fun z => zetaDilation p.1 (-I * z))) :=
    upperEndAnalyticDeriv_iterate_repr p.2 (rotatedZetaAnalytic p.1)
      (fun z => zetaDilation p.1 (-I * z)) rfl
  rw [rotatedPhysicalJet, map_mul, complexAnalytic_repr, hr, ← map_mul]
  congr 1
  ext z
  dsimp only [Pi.mul_apply]
  rw [iteratedDeriv_comp_const_mul_of_ne _ _ (neg_ne_zero.mpr I_ne_zero)]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)), one_mul]

theorem rotatedPhysicalJet_map (p : ℕ × ℕ) :
    algebraMap upperEndAnalyticSubring upperEndMeroField (rotatedPhysicalJet p) =
      algebraMap ℂ upperEndMeroField (((-I) ^ p.2)⁻¹) *
        differentialJet p.2 (rotatedZetaMero p.1) := by
  rw [rotatedPhysicalJet, map_mul, rotatedZetaMero_eq_analytic,
    GaloisForLFunctions.HTGeometry.differentialJet_algebraMap]
  rfl

/-- All physical dilation jets are algebraically independent as functions on `Re s=2`. -/
theorem zetaDilation_jets_line_algebraicIndependent :
    AlgebraicIndependent ℂ
      (fun p : ℕ × ℕ => fun t : ℝ => iteratedDeriv p.2 (zetaDilation p.1) (2 + t * I)) := by
  have hai : AlgebraicIndependent ℂ (fun p : ℕ × ℕ =>
      differentialJet p.2 (rotatedZetaMero p.1)) :=
    AlgebraicIndependent.restrictScalars
      (algebraMap ℂ upperEndRationalCoordinateField).injective
      rotatedZetaMero_differentialIndependent
  have hscale := AlgebraicIndependent.const_mul_coordinates hai
    (fun p : ℕ × ℕ => (((-I) ^ p.2)⁻¹))
    (fun p => inv_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)))
  apply algebraicIndependent_line_of_rotated
    (fun p : ℕ × ℕ => iteratedDeriv p.2 (zetaDilation p.1)) rotatedPhysicalJet
    (fun p => analyticOnNhd_iteratedDeriv (zetaDilation_analytic_right p.1) p.2)
    rotatedPhysicalJet_repr
  simpa only [rotatedPhysicalJet_map] using hscale

/-- Actual positive integer zeta dilates in the common meromorphic field. -/
def zetaDilationMero (n : ℕ) : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField (zetaDilationAnalytic n)

/-- Every positive integer dilation of zeta is jointly differentially independent
of all the others over the actual Gamma differential field. -/
theorem zetaDilation_differentialIndependent_gamma :
    DifferentialIndependent ↥gammaCoefficientField zetaDilationMero := by
  have h := algebraicIndependent_gamma_of_line (by norm_num : (0 : ℝ) < 2)
    (fun p : ℕ × ℕ => (upperEndAnalyticDeriv^[p.2]) (zetaDilationAnalytic p.1))
    (fun p : ℕ × ℕ => iteratedDeriv p.2 (zetaDilation p.1))
    (fun p => upperEndAnalyticDeriv_iterate_repr p.2 (zetaDilationAnalytic p.1)
      (zetaDilation p.1) rfl)
    (fun p => (zetaDilation_jet_line p.1 p.2).1)
    (fun p => (zetaDilation_jet_line p.1 p.2).2)
    zetaDilation_jets_line_algebraicIndependent
  simpa only [DifferentialIndependent, zetaDilationMero, GaloisForLFunctions.HTGeometry.differentialJet_algebraMap] using h

/-- The actual theta constants and `E₂` preserve full integer-dilation freeness. -/
theorem zetaDilation_differentialIndependent_thetaGamma :
    DifferentialIndependent
      ↥ModularThetaCoefficients.thetaGammaCoefficientField zetaDilationMero :=
  (ModularThetaCoefficients.thetaGamma_differentialIndependent_iff _).mpr
    zetaDilation_differentialIndependent_gamma

/-- The zeta family sampled along one multiplicative integer orbit. -/
def mahlerZetaMero (q j : ℕ) : upperEndMeroField := zetaDilationMero (q ^ j - 1)

theorem mahlerZetaMero_differentialIndependent {q : ℕ} (hq : 2 ≤ q) :
    DifferentialIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField
      (mahlerZetaMero q) := by
  have hinj : Function.Injective (fun j : ℕ => q ^ j - 1) := by
    intro j k hjk
    have hj : 0 < q ^ j := pow_pos (by omega) _
    have hk : 0 < q ^ k := pow_pos (by omega) _
    apply Nat.pow_right_injective hq
    change q ^ j = q ^ k
    change q ^ j - 1 = q ^ k - 1 at hjk
    omega
  exact zetaDilation_differentialIndependent_thetaGamma.comp _ hinj

/-- No nonzero finite differential–Mahler polynomial with concrete theta–Gamma
coefficients vanishes on the actual zeta dilation orbit. -/
theorem mahlerZeta_no_polynomial_relation {q : ℕ} (hq : 2 ≤ q)
    (P : MvPolynomial (ℕ × ℕ)
      ↥ModularThetaCoefficients.thetaGammaCoefficientField) (hP : P ≠ 0) :
    MvPolynomial.aeval (fun p : ℕ × ℕ => differentialJet p.2 (mahlerZetaMero q p.1)) P ≠ 0 :=
  fun he => hP ((mahlerZetaMero_differentialIndependent hq).eq_zero_of_aeval_eq_zero P he)

/-- The orbit's analytic representative is exactly `s ↦ ζ(q^j s)`. -/
theorem mahlerZeta_representative {q : ℕ} (hq : 2 ≤ q) (j : ℕ) :
    upperEndAnalyticSubring.subtype (zetaDilationAnalytic (q ^ j - 1)) =
      Germ.coeRingHom upperEndFilter (fun s : ℂ => riemannZeta ((q ^ j : ℕ) * s)) := by
  have hj : 1 ≤ q ^ j := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  change Germ.coeRingHom upperEndFilter (zetaDilation (q ^ j - 1)) = _
  congr 1
  ext s
  rw [zetaDilation, Nat.sub_add_cancel hj]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaJoint
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaJoint.algebraicIndependent_gamma_of_line
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaJoint.zetaDilation_differentialIndependent_gamma
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaJoint.zetaDilation_differentialIndependent_thetaGamma
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaJoint.mahlerZeta_no_polynomial_relation
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaJoint.mahlerZeta_representative
