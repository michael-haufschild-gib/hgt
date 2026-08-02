import GaloisForLFunctions.HTGeometry.DeformedPostcriticalSeparation
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Two jets of the deformed fibre, separated by one postcritical coefficient

Two factorisations of `1 + t^L` over the coefficient field with distinct constant terms produce, over
the universal deformation of the critical observation, two jets that

* have the same critical observation and the same vanishing new raw coefficient, and
* have **different** first postcritical reciprocal coefficients.

That is the fibre statement of the card, for every `(m, n)` with `m, n >= 1`: one postcritical
reciprocal coefficient is not a function of the critical observation and the new raw coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (K : Type*) [Field K] (m n : ℕ)

/-- The deformation parameters have vanishing constant coefficient. -/
theorem deformIdeal_le_ker_constantCoeff :
    deformIdeal K m n
      ≤ RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin n ⊕ Fin m ⊕ Unit) (R := K)) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  simp [RingHom.mem_ker]

/-- **Two jets of the deformed fibre with distinct postcritical reciprocal coefficients.** -/
theorem exists_two_deformed_postcritical_jets {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A₀ B₀ A₁ B₁ : K[X]}
    (hA₀ : A₀.Monic) (hA₀deg : A₀.natDegree = m) (hB₀ : B₀.Monic) (hB₀deg : B₀.natDegree = n)
    (hA₁ : A₁.Monic) (hA₁deg : A₁.natDegree = m) (hB₁ : B₁.Monic) (hB₁deg : B₁.natDegree = n)
    (hcop₀ : IsCoprime A₀ B₀) (hcop₁ : IsCoprime A₁ B₁)
    (hfac₀ : A₀ * B₀ = 1 + X ^ (m + n)) (hfac₁ : A₁ * B₁ = 1 + X ^ (m + n))
    (hsep : A₀.coeff 0 ≠ A₁.coeff 0) :
    ∃ (Z₀ W₀ Z₁ W₁ : (deformBase K m n)[X]) (v₀ v₁ : deformBase K m n),
      (∀ i, m ≤ i → Z₀.coeff i = Z₁.coeff i) ∧
      (∀ j, n ≤ j → W₀.coeff j = W₁.coeff j) ∧
      (X : (deformBase K m n)[X]) ^ (m + n + 1)
        ∣ (Z₀ + Polynomial.C (deformParam K m n) * X ^ (m + n))
          * (W₀ + Polynomial.C v₀ * X ^ (m + n)) - 1 ∧
      (X : (deformBase K m n)[X]) ^ (m + n + 1)
        ∣ (Z₁ + Polynomial.C (deformParam K m n) * X ^ (m + n))
          * (W₁ + Polynomial.C v₁ * X ^ (m + n)) - 1 ∧
      v₀ ≠ v₁ ∧ W₀.coeff (m + n) = 0 ∧ W₁.coeff (m + n) = 0 ∧
      Z₀.natDegree < m + n ∧ Z₁.natDegree < m + n ∧
      (∀ i, m ≤ i → Z₀.coeff i
        = (A₀.map (algebraMap K (deformBase K m n))).coeff i + (rawDeformation K m n).coeff i) ∧
      (∀ j, n ≤ j → W₀.coeff j
        = (B₀.map (algebraMap K (deformBase K m n))).coeff j
          + (reciprocalDeformation K m n).coeff j) := by
  classical
  set φ : K →+* deformBase K m n := algebraMap K (deformBase K m n) with hφ
  set I : Ideal (deformBase K m n) := deformIdeal K m n with hI
  obtain ⟨Z₀, W₀, Z₁, W₁, hdvd₀, hdvd₁, hobsZ, hobsW, hsepZ, hr₀Z, hr₀W, hr₁Z, hr₁W,
      hW₀deg, hW₁deg, hZ₀deg, hZ₁deg, hZdec, hWdec⟩ :=
    exists_two_deformed_pure_factorisations K hm hn hA₀ hA₀deg hB₀ hB₀deg hA₁ hA₁deg hB₁ hB₁deg
      hcop₀ hcop₁ hfac₀ hfac₁ hsep
  -- the pure error is exactly the horizon
  have hpure : ∀ {A B : K[X]}, A * B = 1 + X ^ (m + n) →
      (A.map φ) * (B.map φ) - 1 = (X : (deformBase K m n)[X]) ^ (m + n) := by
    intro A B h
    rw [← Polynomial.map_mul, h, Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_X, add_sub_cancel_left]
  -- the truncated error of each deformed pair is congruent to one
  have hGone : ∀ {A B Z W G : (deformBase K m n)[X]},
      A * B - 1 = (X : (deformBase K m n)[X]) ^ (m + n) →
      inversionError Z W = (X : (deformBase K m n)[X]) ^ (m + n) * G →
      CoeffMem I (Z - A) → CoeffMem I (W - B) → G.coeff 0 - 1 ∈ I := by
    intro A B Z W G hAB hZW hZ hW
    have hshift : (X : (deformBase K m n)[X]) ^ (m + n) * (G - 1)
        = (Z - A) * W + A * (W - B) := by
      have h1 : (X : (deformBase K m n)[X]) ^ (m + n) * G = Z * W - 1 := by
        rw [← hZW, inversionError]
      have h2 : (X : (deformBase K m n)[X]) ^ (m + n) = A * B - 1 := hAB.symm
      rw [mul_sub, mul_one, h1, h2]
      ring
    have hmem : CoeffMem I ((X : (deformBase K m n)[X]) ^ (m + n) * (G - 1)) := by
      rw [hshift]
      refine CoeffMem.add ?_ ?_
      · exact (CoeffMem.mul hZ (fun _ => Submodule.mem_top)).mono (le_of_eq (by rw [Ideal.mul_top]))
      · exact (CoeffMem.mul (fun _ => Submodule.mem_top) hW).mono
          (le_of_eq (by rw [Ideal.top_mul]))
    have := hmem (m + n)
    rwa [coeff_X_pow_mul_eq _ (le_refl _), Nat.sub_self, Polynomial.coeff_sub,
      Polynomial.coeff_one_zero] at this
  -- the constant terms are units
  have hunit : ∀ {A : K[X]} {Z : (deformBase K m n)[X]}, A.coeff 0 ≠ 0 →
      CoeffMem I (Z - A.map φ) → IsUnit (Z.coeff 0) := by
    intro A Z hA0 hZ
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    have hker := deformIdeal_le_ker_constantCoeff K m n
    have hmem : Z.coeff 0 - (A.map φ).coeff 0 ∈ I := by
      have := hZ 0
      rwa [Polynomial.coeff_sub] at this
    have hzero := hker hmem
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hzero
    rw [hzero, Polynomial.coeff_map, MvPowerSeries.algebraMap_apply,
      MvPowerSeries.constantCoeff_C]
    simpa using hA0.isUnit
  have hconst : ∀ {A B : K[X]}, A * B = 1 + X ^ (m + n) → A.coeff 0 * B.coeff 0 = 1 := by
    intro A B h
    have h0 : (A * B).coeff 0 = ((1 : K[X]) + X ^ (m + n)).coeff 0 := by rw [h]
    rwa [Polynomial.mul_coeff_zero, Polynomial.coeff_add, Polynomial.coeff_one_zero,
      Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 = m + n)), add_zero] at h0
  have hA₀0 : A₀.coeff 0 ≠ 0 := by
    intro hcon
    have h := hconst hfac₀
    rw [hcon, zero_mul] at h
    exact zero_ne_one h
  have hA₁0 : A₁.coeff 0 ≠ 0 := by
    intro hcon
    have h := hconst hfac₁
    rw [hcon, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨G₀, hG₀⟩ := hdvd₀
  obtain ⟨G₁, hG₁⟩ := hdvd₁
  have hZW₀ : Z₀ * W₀ - 1 = (X : (deformBase K m n)[X]) ^ (m + n) * G₀ := by
    rw [← hG₀, inversionError]
  have hZW₁ : Z₁ * W₁ - 1 = (X : (deformBase K m n)[X]) ^ (m + n) * G₁ := by
    rw [← hG₁, inversionError]
  obtain ⟨v₀, hrel₀, hv₀⟩ :=
    exists_postcritical_coefficient (deformParam K m n) (by omega) hZW₀ (hunit hA₀0 hr₀Z)
  obtain ⟨v₁, hrel₁, hv₁⟩ :=
    exists_postcritical_coefficient (deformParam K m n) (by omega) hZW₁ (hunit hA₁0 hr₁Z)
  refine ⟨Z₀, W₀, Z₁, W₁, v₀, v₁, hobsZ, hobsW, hv₀, hv₁, ?_,
    Polynomial.coeff_eq_zero_of_natDegree_lt hW₀deg,
    Polynomial.coeff_eq_zero_of_natDegree_lt hW₁deg, hZ₀deg, hZ₁deg, hZdec, hWdec⟩
  intro hcon
  refine postcritical_separates (by omega) (deformParam_mem K m n) hZW₀ hZW₁
    (hGone (hpure hfac₀) hG₀ hr₀Z hr₀W)
    (hGone (hpure hfac₁) hG₁ hr₁Z hr₁W) hv₀ hv₁ hsepZ ?_
  rw [hcon, sub_self]
  exact Submodule.zero_mem _

end GaloisForLFunctions.HTGeometry
