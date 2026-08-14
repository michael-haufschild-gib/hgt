import GaloisForLFunctions.RHTower.CompactCarrierPolynomialDetection
import GaloisForLFunctions.RHTower.WeightedEulerCarrierTangent
import GaloisForLFunctions.HTGeometry.HolomorphicOnOpen
import GaloisForLFunctions.HTGeometry.CompactOpenDualCarrier
import GaloisForLFunctions.HTGeometry.CarrierComplexFunctional
import GaloisForLFunctions.HTGeometry.ConvexCarrierCauchyVanishing
import GaloisForLFunctions.HTGeometry.CarrierAnnihilatesHolomorphicPompeiu
import GaloisForLFunctions.HTGeometry.LocallyConvexDenseOfVanishingDual

/-!
# Prime Euler unit tangents are complete on every bounded convex right-half-plane domain

Let `D` be an open convex set whose points all have positive real part.  A continuous functional on
its holomorphic functions is carried by a compact subset, and the convex hull of that carrier is
still a compact subset of `D`.  Hahn–Banach turns the functional into a complex functional on the
continuous functions of the hull; annihilating a cofinite set of prime Euler tangents makes its
Fourier–Borel transform vanish by the Lambert–Möbius sector argument, hence it kills every power of
the carrier coordinate.  Convexity of the hull then makes its Cauchy transform vanish on the whole
complement, and Cauchy–Pompeiu turns that into annihilation of every function holomorphic on `D`.

Consequently the complex span of the tangents `w_p = (log p) p^{-s}/(1 - p^{-s})²`, `p` outside any
prescribed finite set, is dense in the holomorphic functions of `D` for the compact-open topology.

* `RHTower.holoOn_eq_zero_of_annihilates_eulerTangent`;
* `RHTower.topologicalClosure_span_eulerTangentOn_eq_top`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The prime Euler unit tangent on a domain of the right half plane. -/
def eulerTangentMapOn (D : Set ℂ) (hD : D ⊆ {s : ℂ | 0 < s.re}) (p : Nat.Primes) : C(D, ℂ) :=
  ⟨fun z => eulerTangent (p : ℕ) (z : ℂ),
    ((differentiableOn_eulerTangent p.2).continuousOn.mono hD).restrict⟩

theorem eulerTangentMapOn_mem (D : Set ℂ) (hD : D ⊆ {s : ℂ | 0 < s.re}) (p : Nat.Primes) :
    eulerTangentMapOn D hD p ∈ holoOn D :=
  ⟨eulerTangent (p : ℕ), (differentiableOn_eulerTangent p.2).mono hD, fun _ => rfl⟩

/-- The prime Euler unit tangent as an element of the holomorphic space of the domain. -/
def eulerTangentOn (D : Set ℂ) (hD : D ⊆ {s : ℂ | 0 < s.re}) (p : Nat.Primes) : holoOn D :=
  ⟨eulerTangentMapOn D hD p, eulerTangentMapOn_mem D hD p⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Cofinite annihilation of the prime Euler tangents kills every continuous functional on a
convex right-half-plane domain.** -/
theorem holoOn_eq_zero_of_annihilates_eulerTangent
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hDre : D ⊆ {s : ℂ | 0 < s.re})
    (S : Finset Nat.Primes) (ell : holoOn D →L[ℝ] ℝ)
    (hann : ∀ p : Nat.Primes, p ∉ S →
      ell (eulerTangentOn D hDre p) = 0 ∧ ell (holoOnImul D (eulerTangentOn D hDre p)) = 0) :
    ∀ y : holoOn D, ell y = 0 := by
  classical
  obtain ⟨K₀, C₀, hK₀, hC₀, hbnd⟩ := exists_compact_dual_bound (holoOn D) ell
  set K₁ : Set ℂ := (Subtype.val : ↥D → ℂ) '' K₀ with hK₁def
  have hK₁ : IsCompact K₁ := hK₀.image continuous_subtype_val
  have hK₁D : K₁ ⊆ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨K, hKcompact, hKconv, hK₁K, hKD⟩ :=
    exists_compact_convex_between hK₁ hDopen hDconv hK₁D
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  set T : holoOn D →ₗ[ℝ] C(K, ℂ) := holoOnRestrict hKD with hT
  -- the functional is dominated by the supremum norm on the hull
  have hbd : ∀ g : holoOn D, |ell.toLinearMap g| ≤ C₀ * ‖T g‖ := by
    intro g
    refine hbnd g ‖T g‖ (norm_nonneg _) ?_
    intro x hx
    have hmem : ((x : ℂ)) ∈ K := hK₁K ⟨x, hx, rfl⟩
    have hxeq : (⟨(x : ℂ), hKD hmem⟩ : (D : Set ℂ)) = x := Subtype.ext rfl
    have hval : (g : C((D : Set ℂ), ℂ)) x = T g ⟨(x : ℂ), hmem⟩ := by
      rw [hT, holoOnRestrict_apply, hxeq]
    rw [hval]
    exact (T g).norm_coe_le_norm _
  obtain ⟨L, hL⟩ := exists_complex_functional_of_bound (M := ↥(holoOn D)) (K := ↥K)
    T ell.toLinearMap C₀ hbd
  -- the complex functional annihilates the restricted tangents
  have hLann : ∀ p : Nat.Primes, p ∉ S → L (T (eulerTangentOn D hDre p)) = 0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hann p hp
    have hre : (L (T (eulerTangentOn D hDre p))).re = 0 := by
      rw [hL (eulerTangentOn D hDre p)]
      exact h1
    have hTi : T (holoOnImul D (eulerTangentOn D hDre p))
        = Complex.I • T (eulerTangentOn D hDre p) := rfl
    have him : (Complex.I * L (T (eulerTangentOn D hDre p))).re = 0 := by
      have := hL (holoOnImul D (eulerTangentOn D hDre p))
      rw [hTi, map_smul, smul_eq_mul] at this
      rw [this]
      exact h2
    rw [Complex.mul_re] at him
    simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_eq_zero] at him
    exact Complex.ext hre him
  -- carrier geometry
  have hαex : ∃ α : ℝ, 0 < α ∧ ∀ z ∈ K, α ≤ z.re := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMinOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => z.re))
      exact ⟨z₀.re, hDre (hKD hz₀K), fun z hz => hz₀ hz⟩
  obtain ⟨α, hα, hαK⟩ := hαex
  have hMex : ∃ M : ℝ, ∀ z ∈ K, |z.im| ≤ M := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨0, fun z hz => absurd (hemp ▸ hz) (by simp)⟩
    · obtain ⟨z₀, hz₀K, hz₀⟩ := hKcompact.exists_isMaxOn hne
        (Continuous.continuousOn (by fun_prop : Continuous fun z : ℂ => |z.im|))
      exact ⟨|z₀.im|, fun z hz => hz₀ hz⟩
  obtain ⟨M, hMK⟩ := hMex
  -- the restricted tangent is the compact-carrier tangent of the coordinate
  have hTe : ∀ p : Nat.Primes,
      T (eulerTangentOn D hDre p) = compactPrimeEulerUnitTangent (coordMap K) (p : ℕ) := by
    intro p
    ext z
    rw [compactPrimeEulerUnitTangent_coordMap hα (fun w hw => hαK w hw) p.2.two_le z]
    rfl
  -- the Fourier--Borel transform vanishes
  set B : ℝ := ∑ q ∈ S, Real.log ((q : Nat.Primes) : ℝ) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    positivity
  set R₀ : ℝ := 1 + B with hR₀def
  have hR₀ : 0 < R₀ := by rw [hR₀def]; linarith
  have hannBig : ∀ p : Nat.Primes, R₀ + 1 < Real.log ((p : ℕ) : ℝ) →
      L (compactPrimeEulerUnitTangent (coordMap K) (p : ℕ)) = 0 := by
    intro p hp
    have hpnot : p ∉ S := by
      intro hpS
      have hlognonneg : ∀ q ∈ S, 0 ≤ Real.log ((q : Nat.Primes) : ℝ) := by
        intro q _
        exact Real.log_nonneg (by exact_mod_cast q.prop.one_lt.le)
      have hle : Real.log ((p : Nat.Primes) : ℝ) ≤ B := by
        rw [hB]
        exact Finset.single_le_sum hlognonneg hpS
      rw [hR₀def] at hp
      have : Real.log ((p : ℕ) : ℝ) = Real.log ((p : Nat.Primes) : ℝ) := rfl
      rw [this] at hp
      linarith
    rw [← hTe p]
    exact hLann p hpnot
  have hF := compactFourierBorel_eq_zero_of_tangent_annihilation_rightRectangle
    L (coordMap K) α M R₀ hα hR₀ (fun k => hαK (k : ℂ) k.2) (fun k => hMK (k : ℂ) k.2) hannBig
  have hpow : ∀ N : ℕ, L (coordMap K ^ N) = 0 :=
    fun N => map_coordinate_pow_eq_zero_of_fourierBorel_zero L (coordMap K) hF N
  have hzero := cauchyTransform_eq_zero_of_convex hKcompact hKconv L hpow
  -- Cauchy--Pompeiu finishes
  intro y
  obtain ⟨G, hG, hGy⟩ := y.2
  have hTy : ∀ z : K, T y z = G (z : ℂ) := by
    intro z
    rw [hT, holoOnRestrict_apply]
    exact hGy _
  have hLy := apply_eq_zero_of_cauchyTransform_eq_zero_of_isOpen (K := K)
    hKcompact hDopen hKD hG L hzero (T y) hTy
  have hfin := hL y
  rw [hLy] at hfin
  simpa using hfin.symm

/-- The tangent family indexed by the retained primes and the two real directions. -/
def eulerTangentOnFamily (D : Set ℂ) (hD : D ⊆ {s : ℂ | 0 < s.re}) (S : Finset Nat.Primes) :
    {p : Nat.Primes // p ∉ S} × Bool → holoOn D :=
  fun q => if q.2 then holoOnImul D (eulerTangentOn D hD (q.1 : Nat.Primes))
    else eulerTangentOn D hD (q.1 : Nat.Primes)

/-- **The cofinite prime Euler tangents span a dense subspace of the holomorphic functions on a
bounded convex right-half-plane domain.**  Their real span together with the `i`-multiples is the
complex span, so this is complex-span density in the compact-open topology. -/
theorem topologicalClosure_span_eulerTangentOn_eq_top
    {D : Set ℂ} (hDopen : IsOpen D) (hDconv : Convex ℝ D) (hDre : D ⊆ {s : ℂ | 0 < s.re})
    (S : Finset Nat.Primes) :
    (Submodule.span ℝ (Set.range (eulerTangentOnFamily D hDre S))).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs
    (E := holoOn D) (Submodule.span ℝ (Set.range (eulerTangentOnFamily D hDre S))) ?_
  intro ell hell
  have hann : ∀ p : Nat.Primes, p ∉ S →
      ell (eulerTangentOn D hDre p) = 0 ∧ ell (holoOnImul D (eulerTangentOn D hDre p)) = 0 := by
    intro p hp
    constructor
    · refine hell _ (Submodule.subset_span ⟨(⟨p, hp⟩, false), ?_⟩)
      simp [eulerTangentOnFamily]
    · refine hell _ (Submodule.subset_span ⟨(⟨p, hp⟩, true), ?_⟩)
      simp [eulerTangentOnFamily]
  exact ContinuousLinearMap.ext
    (holoOn_eq_zero_of_annihilates_eulerTangent hDopen hDconv hDre S ell hann)

end RHTower
