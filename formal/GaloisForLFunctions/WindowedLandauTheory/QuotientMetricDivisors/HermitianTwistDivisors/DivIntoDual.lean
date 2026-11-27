import GaloisForLFunctions.WindowedLandauTheory.QuotientMetricDivisors.StatementACE

/-! A divisor functional integral on the local lattices is integral on
the global lattice. Denominators outside the given prime have valuation zero. -/

open NumberField IsDedekindDomain
open scoped Matrix

namespace WindowedLandauTheory.DivisionValues

variable {K : Type} [Field K] [NumberField K]

private theorem vw_algebraMap_eq_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∉ w.asIdeal) : vw w (algebraMap (𝓞 K) K s) = 0 := by
  classical
  have hs0 : s ≠ 0 := fun h => hs (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {s} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hs0
  have hnd : ¬ w.asIdeal ∣ Ideal.span {s} := fun h => hs (Ideal.dvd_span_singleton.mp h)
  have hirr : Irreducible w.asIdeal := (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible
  have hc := not_not.mp (mt (Associates.count_ne_zero_iff_dvd hJ hirr).mp hnd)
  rw [vw, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ,
    Nat.cast_eq_zero]
  exact hc

private theorem vw_mul_nonzero (w : HeightOneSpectrum (𝓞 K)) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) : vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w
    (fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))
    (fun h => hb (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))]

/-- A valuation bound on the original lattice transfers through the matrix
images and localization at the chosen prime. -/
theorem reduction_first_step : StepA := by
  intro K _ _ _ w n D M π J B P ζ σ hζ hvζ hP hM x hx
  obtain ⟨s, hs, y, hy, hyx⟩ := hx
  obtain ⟨F, hF, hFy⟩ := hy
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hFy hyx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ w.asIdeal.zero_mem)
  have hsK : algebraMap (𝓞 K) K s ≠ 0 :=
    fun h => hs0 ((IsFractionRing.injective (𝓞 K) K) (h.trans (map_zero _).symm))
  have hPF : P F = ζ * (algebraMap (𝓞 K) K s * B x) := by
    rw [hP F, hFy, hyx, ← algebraMap_smul K s x, map_smul, smul_eq_mul]
  by_cases hBx : B x = 0
  · exact Or.inl hBx
  · have hPF0 : P F ≠ 0 := by
      rw [hPF]
      exact mul_ne_zero hζ (mul_ne_zero hsK hBx)
    have hσ := (hM F hF).resolve_left hPF0
    rw [hPF, vw_mul_nonzero w hζ (mul_ne_zero hsK hBx), vw_mul_nonzero w hsK hBx,
      hvζ, vw_algebraMap_eq_zero w hs, zero_add, zero_add] at hσ
    exact Or.inr hσ

namespace DualLatticeDivisor

/-- Nonnegative multiplicities make the principal fractional ideal an
integral ideal, so its generator lies in the ring of integers. -/
theorem mem_range_of_vw_nonneg (a : K) (ha : a ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) :
    a ∈ Set.range (algebraMap (𝓞 K) K) := by
  classical
  let I := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a
  have hI : I ≠ 0 := fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
  have hprod : ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 K),
        (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (FractionalIdeal.count K w I) := by
    refine finprod_induction
      (fun A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K =>
        ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = A)
      ⟨1, by simp⟩ ?_ ?_
    · rintro x y ⟨J₁, h₁⟩ ⟨J₂, h₂⟩
      exact ⟨J₁ * J₂, by rw [FractionalIdeal.coeIdeal_mul, h₁, h₂]⟩
    · intro w
      have hw : 0 ≤ FractionalIdeal.count K w I := h w
      refine ⟨w.asIdeal ^ (FractionalIdeal.count K w I).toNat, ?_⟩
      rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, Int.toNat_of_nonneg hw]
  rw [FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI] at hprod
  obtain ⟨J, hJ⟩ := hprod
  have hmem : a ∈ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hJ]
    exact FractionalIdeal.mem_spanSingleton_self _ a
  obtain ⟨y, -, hy⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmem
  exact ⟨y, hy⟩

end DualLatticeDivisor

open HermitianLatticesTheory in
/-- Local divisibility at every finite place gives an integral value
of the divisor functional on the global lattice. -/
theorem divisor_into_dual_lattice (K : Type) [Field K] [NumberField K] [StarRing K]
    (D : ℕ) (R : Submodule (𝓞 K) (Fin D → K)) (B : (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (J : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K)
    (hζ : ∀ w, ζ w ≠ 0) (hvζ : ∀ w, vw w (ζ w) = 0)
    (hP : ∀ w (F : Fin (n w) → K), P w F = ζ w * B ((J w).mulVec ((π w).mulVec F)))
    (hM : ∀ w, ∀ F ∈ M w, P w F = 0 ∨ 0 ≤ vw w (P w F))
    (hloc : ∀ w, localization₂ w.asIdeal R =
      localization₂ w.asIdeal (matLat (J w) (matLat (π w) (M w)))) :
    ∀ x ∈ R, B x ∈ Set.range (algebraMap (𝓞 K) K) := by
  intro x hx
  by_cases hBx : B x = 0
  · exact ⟨0, (map_zero _).trans hBx.symm⟩
  · refine DualLatticeDivisor.mem_range_of_vw_nonneg _ hBx fun w => ?_
    have hxl : x ∈ localization₂ w.asIdeal R :=
      ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hloc w] at hxl
    exact (reduction_first_step K w (n w) D (M w) (π w) (J w) B (P w) (ζ w) 0
      (hζ w) (hvζ w) (hP w) (hM w) x hxl).resolve_left hBx

end WindowedLandauTheory.DivisionValues
