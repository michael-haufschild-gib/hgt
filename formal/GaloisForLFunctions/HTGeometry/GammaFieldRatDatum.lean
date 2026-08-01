import GaloisForLFunctions.HTGeometry.UpperEndGammaElement
import GaloisForLFunctions.HTGeometry.DigammaRationalFieldDatum
import GaloisForLFunctions.HTGeometry.GammaShapeDominantResidue

/-!
# The Gamma field over the rational base

An element of the differential algebra generated over `ℂ(s)` by `Γ` is, after multiplication by one
nonzero polynomial, an analytic germ of the form `∑_j Γ^{u_j}·C_j` with pairwise distinct exponents
`u_j` and each `C_j` a jet polynomial in the polygammas with polynomial coefficients.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaRatDatumDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaRatDatumIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaRatDatumDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaRatDatumComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaRatDatumRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- What holds at the upper end holds along every vertical line. -/
theorem eventually_line_of_upperEnd {p : ℂ → Prop} (h : ∀ᶠ z : ℂ in upperEndFilter, p z) (σ : ℝ) :
    ∀ᶠ t : ℝ in atTop, p ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  rw [upperEndFilter_basis.eventually_iff] at h
  obtain ⟨H, -, hH⟩ := h
  filter_upwards [eventually_gt_atTop H] with t ht
  refine hH ?_
  show H < ((σ : ℂ) + (t : ℂ) * Complex.I).im
  simpa using ht

/-- **Clearing an element of the Gamma jet algebra.**  One nonzero polynomial turns it into an
analytic germ that is a `Γ`-polynomial with jet-polynomial coefficients. -/
theorem exists_gammaAlgebra_clearing {y : upperEndMeroField}
    (hy : y ∈ differentialJetAlgebra (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField)) :
    ∃ (q : Polynomial ℂ) (N : ℕ) (u : Fin N → ℕ) (C : Fin N → upperEndAnalyticSubring),
      q ≠ 0 ∧ Function.Injective u
        ∧ upperEndPolyToMero q * y = algebraMap upperEndAnalyticSubring upperEndMeroField
            (∑ j : Fin N, gammaUpperAnalytic ^ u j * C j)
        ∧ ∀ j : Fin N, ∃ (M K : ℕ) (p : Fin M → Polynomial ℂ) (E : Fin M → Fin (K + 1) → ℕ),
            Function.Injective E ∧ upperEndAnalyticSubring.subtype (C j)
              = Germ.coeRingHom upperEndFilter (fun z : ℂ => ∑ α : Fin M, (p α).eval z
                * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E α i) := by
  classical
  obtain ⟨N, u, A, huinj, hAmem, hy'⟩ := exists_gamma_expansion (gammaJetAlgebra_le_ratAdjoin hy)
  choose q M K p E B hq hEinj hqA hgerm using fun j : Fin N => exists_ratAlgebra_analytic (hAmem j)
  have hQ0 : (∏ j : Fin N, q j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hq j
  have hsplit : ∀ j : Fin N, (∏ k : Fin N, q k) = q j * ∏ k ∈ Finset.univ.erase j, q k :=
    fun j => (Finset.mul_prod_erase Finset.univ q (Finset.mem_univ j)).symm
  have hterm : ∀ j : Fin N, upperEndPolyToMero (∏ k : Fin N, q k) * A j
      = algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndPolyToAnalytic (∏ k ∈ Finset.univ.erase j, q k) * B j) := by
    intro j
    rw [map_mul, hsplit j, map_mul,
      mul_comm (upperEndPolyToMero (q j)) (upperEndPolyToMero (∏ k ∈ Finset.univ.erase j, q k)),
      mul_assoc, hqA j]
    rfl
  refine ⟨∏ j : Fin N, q j, N, u,
    fun j => upperEndPolyToAnalytic (∏ k ∈ Finset.univ.erase j, q k) * B j, hQ0, huinj, ?_, ?_⟩
  · rw [hy', Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, ← hterm j, ← gammaUpperMero]
    ring
  · intro j
    refine ⟨M j, K j, fun α => (∏ k ∈ Finset.univ.erase j, q k) * p j α, E j, hEinj j, ?_⟩
    rw [map_mul, hgerm j, polyToAnalytic_subtype, ← map_mul]
    congr 1
    funext z
    simp only [Pi.mul_apply, Polynomial.eval_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring

/-- **The datum of a nonzero element of the Gamma jet algebra.**  Its cleared analytic germ has a
residue against a `gammaJetShape`: the smallest power of `Γ` present dominates, and inside that power
the digamma datum decides. -/
theorem exists_gammaAlgebra_datum {σ : ℝ} (hσ : 0 < σ) {y : upperEndMeroField}
    (hy : y ∈ differentialJetAlgebra (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hy0 : y ≠ 0) :
    ∃ (q : Polynomial ℂ) (W : upperEndAnalyticSubring) (G : ℂ → ℂ) (u a d b : ℕ) (r : ℂ),
      q ≠ 0 ∧ r ≠ 0
        ∧ upperEndPolyToMero q * y = algebraMap upperEndAnalyticSubring upperEndMeroField W
        ∧ upperEndAnalyticSubring.subtype W = Germ.coeRingHom upperEndFilter G
        ∧ Tendsto (fun t : ℝ => G ((σ : ℂ) + (t : ℂ) * Complex.I)
            / gammaJetShape σ u a d b t) atTop (nhds r) := by
  classical
  obtain ⟨q, N, u, C, hq, huinj, heq, hCdata⟩ := exists_gammaAlgebra_clearing hy
  choose M K p E hEinj hCgerm using hCdata
  -- the line function of each coefficient
  set g : Fin N → ℝ → ℂ := fun j t => ∑ α : Fin (M j), (p j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
    * ∏ i : Fin (K j + 1), iteratedDeriv (i : ℕ) Complex.digamma
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i with hg
  set G : ℂ → ℂ := fun z => ∑ j : Fin N, Complex.Gamma z ^ u j
    * ∑ α : Fin (M j), (p j α).eval z
      * ∏ i : Fin (K j + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E j α i with hG
  have hgammaSub : upperEndAnalyticSubring.subtype gammaUpperAnalytic
      = Germ.coeRingHom upperEndFilter (fun z : ℂ => Complex.Gamma z) := rfl
  have hWgerm : upperEndAnalyticSubring.subtype (∑ j : Fin N, gammaUpperAnalytic ^ u j * C j)
      = Germ.coeRingHom upperEndFilter G := by
    have hterm : ∀ j : Fin N,
        upperEndAnalyticSubring.subtype (gammaUpperAnalytic ^ u j * C j)
          = Germ.coeRingHom upperEndFilter (fun z : ℂ => Complex.Gamma z ^ u j
            * ∑ α : Fin (M j), (p j α).eval z
              * ∏ i : Fin (K j + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E j α i) := by
      intro j
      rw [map_mul, map_pow, hCgerm j, hgammaSub, ← map_pow, ← map_mul]
      refine congrArg _ ?_
      funext z
      simp only [Pi.mul_apply, Pi.pow_apply]
    rw [map_sum, Finset.sum_congr rfl fun j _ => hterm j, ← map_sum, hG]
    refine congrArg _ ?_
    funext z
    simp only [Finset.sum_apply]
  -- the line terms
  set F : Fin N → ℝ → ℂ := fun j t => gammaLine σ t ^ u j * g j t with hF
  have hGline : ∀ t : ℝ, G ((σ : ℂ) + (t : ℂ) * Complex.I) = ∑ j : Fin N, F j t := by
    intro t
    simp only [hG, hF, hg, gammaLine]
  -- coefficients that vanish contribute nothing on the line
  have hzero : ∀ j : Fin N, C j = 0 → ∀ᶠ t : ℝ in atTop, g j t = 0 := by
    intro j hCj
    have h1 : Germ.coeRingHom upperEndFilter (fun z : ℂ => ∑ α : Fin (M j), (p j α).eval z
        * ∏ i : Fin (K j + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E j α i) = 0 := by
      rw [← hCgerm j, hCj, map_zero]
    have h2 : Germ.coeRingHom upperEndFilter ((0 : ℂ → ℂ)) = 0 := map_zero _
    have hcoe : ((fun z : ℂ => ∑ α : Fin (M j), (p j α).eval z
        * ∏ i : Fin (K j + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ E j α i : ℂ → ℂ)
          : Germ upperEndFilter ℂ) = ((0 : ℂ → ℂ) : Germ upperEndFilter ℂ) := h1.trans h2.symm
    have hev := eventually_line_of_upperEnd (Filter.Germ.coe_eq.mp hcoe) σ
    filter_upwards [hev] with t ht
    simpa [hg] using ht
  have hWne : (∑ j : Fin N, gammaUpperAnalytic ^ u j * C j) ≠ 0 := by
    intro h
    rw [h, map_zero] at heq
    exact mul_ne_zero (fun hz => hq (upperEndPolyToMero_injective (by rw [hz, map_zero]))) hy0 heq
  have hSne : (Finset.univ.filter (fun j : Fin N => C j ≠ 0)).Nonempty := by
    by_contra hempty
    refine hWne ?_
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    refine Finset.sum_eq_zero fun j _ => ?_
    have hCj : C j = 0 := by
      by_contra hne
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩) (by rw [hempty]; simp)
    rw [hCj, mul_zero]
  obtain ⟨N', ι, hιinj, hιmem, hιsurj, hιsum⟩ :=
    exists_fin_reindex_of_finset (A := ℝ → ℂ) (Finset.univ.filter (fun j : Fin N => C j ≠ 0)) F
  have hN' : 0 < N' := by
    obtain ⟨j, hj⟩ := hSne
    obtain ⟨i, -⟩ := hιsurj j hj
    exact Fin.pos i
  have hCιne : ∀ i : Fin N', C (ι i) ≠ 0 := fun i => (Finset.mem_filter.mp (hιmem i)).2
  -- each surviving term has a Gamma-jet residue
  have hres : ∀ i : Fin N', ∃ (a d b : ℕ) (r : ℂ), r ≠ 0 ∧
      Tendsto (fun t : ℝ => F (ι i) t / gammaJetShape σ (u (ι i)) a d b t) atTop (nhds r) := by
    intro i
    obtain ⟨a, d, b, r, hr, hlim⟩ :=
      exists_polyCoeff_jet_datum hσ (p (ι i)) (E (ι i)) (hEinj (ι i)) (hCιne i) (hCgerm (ι i))
    exact ⟨a, d, b, r, hr, tendsto_div_gammaJetShape_of_polyDatum hσ (u (ι i)) hlim⟩
  choose a d b r hr hreslim using hres
  obtain ⟨β, hβ⟩ := exists_dominant_gammaShape_residue_of_injective hσ hN'
    (fun i => F (ι i)) (fun i => u (ι i)) a d b r (fun i i' hii' => hιinj (huinj hii')) hreslim
  refine ⟨q, ∑ j : Fin N, gammaUpperAnalytic ^ u j * C j, G, u (ι β), a β, d β, b β, r β,
    hq, hr β, heq, hWgerm, ?_⟩
  refine hβ.congr' ?_
  have hallzero : ∀ᶠ t : ℝ in atTop,
      ∀ j ∈ Finset.univ \ Finset.univ.filter (fun j : Fin N => C j ≠ 0), F j t = 0 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hCj : C j = 0 := by
      by_contra hne
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩)
    filter_upwards [hzero j hCj] with t ht
    rw [hF]
    simp [ht]
  filter_upwards [hallzero] with t ht
  have hsum : ∑ i : Fin N', F (ι i) t = ∑ j : Fin N, F j t := by
    have h1 : ∑ j ∈ Finset.univ.filter (fun j : Fin N => C j ≠ 0), F j t
        = ∑ i : Fin N', F (ι i) t := by
      have hev := congrFun hιsum t
      simpa [Finset.sum_apply] using hev
    have h2 : ∑ j ∈ Finset.univ.filter (fun j : Fin N => C j ≠ 0), F j t
        = ∑ j : Fin N, F j t := by
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
      exact ht j (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)
    rw [← h1, h2]
  rw [hGline t, ← hsum]

/-- **Every nonzero element of the Gamma field over the rational base has a datum.**  Clearing the
field denominator and the coefficient denominators presents it as a quotient of two analytic germs,
each a `Γ`-polynomial with jet-polynomial coefficients, and each with a residue against a
`gammaJetShape`; the quotient of the two residues is nonzero. -/
theorem exists_gammaField_datum {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ (q₁ q₂ : Polynomial ℂ) (U V : upperEndAnalyticSubring) (G H : ℂ → ℂ)
      (u₁ a₁ d₁ b₁ u₂ a₂ d₂ b₂ : ℕ) (r : ℂ),
      q₁ ≠ 0 ∧ q₂ ≠ 0 ∧ r ≠ 0
        ∧ x = (upperEndPolyToMero q₂
              * algebraMap upperEndAnalyticSubring upperEndMeroField U)
            / (upperEndPolyToMero q₁
              * algebraMap upperEndAnalyticSubring upperEndMeroField V)
        ∧ upperEndAnalyticSubring.subtype U = Germ.coeRingHom upperEndFilter G
        ∧ upperEndAnalyticSubring.subtype V = Germ.coeRingHom upperEndFilter H
        ∧ Tendsto (fun t : ℝ =>
            (G ((σ : ℂ) + (t : ℂ) * Complex.I) / gammaJetShape σ u₁ a₁ d₁ b₁ t)
            / (H ((σ : ℂ) + (t : ℂ) * Complex.I) / gammaJetShape σ u₂ a₂ d₂ b₂ t))
          atTop (nhds r) := by
  classical
  obtain ⟨D, hDmem, hD0, hxD⟩ := exists_jetAlgebra_denominator (F := RatFunc ℂ) hx
  have hxD0 : x * D ≠ 0 := mul_ne_zero hx0 hD0
  obtain ⟨q₁, U, G, u₁, a₁, d₁, b₁, r₁, hq₁, hr₁, hU, hGgerm, hGlim⟩ :=
    exists_gammaAlgebra_datum hσ hxD hxD0
  obtain ⟨q₂, V, H, u₂, a₂, d₂, b₂, r₂, hq₂, hr₂, hV, hHgerm, hHlim⟩ :=
    exists_gammaAlgebra_datum hσ hDmem hD0
  have hq₁mero : upperEndPolyToMero q₁ ≠ 0 := fun h =>
    hq₁ (upperEndPolyToMero_injective (by rw [h, map_zero]))
  have hq₂mero : upperEndPolyToMero q₂ ≠ 0 := fun h =>
    hq₂ (upperEndPolyToMero_injective (by rw [h, map_zero]))
  have hVne : algebraMap upperEndAnalyticSubring upperEndMeroField V ≠ 0 := by
    rw [← hV]
    exact mul_ne_zero hq₂mero hD0
  have hxeq : x = (upperEndPolyToMero q₂
        * algebraMap upperEndAnalyticSubring upperEndMeroField U)
      / (upperEndPolyToMero q₁
        * algebraMap upperEndAnalyticSubring upperEndMeroField V) := by
    rw [← hU, ← hV]
    field_simp
  have hquot : Tendsto (fun t : ℝ =>
      (G ((σ : ℂ) + (t : ℂ) * Complex.I) / gammaJetShape σ u₁ a₁ d₁ b₁ t)
      / (H ((σ : ℂ) + (t : ℂ) * Complex.I) / gammaJetShape σ u₂ a₂ d₂ b₂ t))
      atTop (nhds (r₁ / r₂)) := hGlim.div hHlim hr₂
  exact ⟨q₁, q₂, U, V, G, H, u₁, a₁, d₁, b₁, u₂, a₂, d₂, b₂, r₁ / r₂,
    hq₁, hq₂, div_ne_zero hr₁ hr₂, hxeq, hGgerm, hHgerm, hquot⟩

end

end GaloisForLFunctions.HTGeometry
