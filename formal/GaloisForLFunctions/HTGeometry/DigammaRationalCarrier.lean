import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.RationalIteratedDeriv

/-!
# The digamma carrier plus a rational function stays hypertranscendental

For `M ≠ 0` and any rational function `A/B` (`B ≠ 0`), the carrier `M·ψ(t) + A(t)/B(t)` is
hypertranscendental.  This closes the single-orbit / nonzero-charge direction of the
signed-archimedean orbit-charge law: after the charge collapse
`∑_j m_j ψ(w+n_j) = M·ψ(w) + rational` (`iteratedDeriv_digamma_charge_general`, `M = ∑ m_j ≠ 0`),
the surviving carrier is exactly of this shape.

A hypothetical algebraic differential relation `Q` for the carrier is transported into a
polynomial-coefficient jet annihilator `P` of the pure digamma jets.  The transport is the affine jet
substitution `Y_j ↦ M·Y_j + (A/B)⁽ʲ⁾(point)`; its rational part is denominator-cleared to the common
power `B^{n+1}` (all jets `(A/B)⁽ʲ⁾ = C_j/B^{j+1} = C_j·B^{n-j}/B^{n+1}`, `j ≤ n`), and the resulting
per-monomial scale mismatch is absorbed by homogeneous-degree bookkeeping.  `B·P` annihilates the
digamma jets off *every* pole (the `B` factor covers the zeros of `B`), so `B·P = 0` by the
polynomial-coefficient Hölder theorem `polyJetEval_offPole_eq_zero`, hence `P = 0`.  Over `RatFunc ℂ`
the same substitution is an affine isomorphism, so `P ≠ 0` — a contradiction.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-! ## Generic multivariate-polynomial lemmas -/

/-- **Homogeneous variable scaling.**  Evaluating a homogeneous polynomial of degree `e` with every
variable scaled by a constant `c` multiplies the value by `cᵉ`. -/
theorem isHomogeneous_eval₂_scale {σ : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
    {e : ℕ} {φ : MvPolynomial σ R} (hφ : φ.IsHomogeneous e) (f : R →+* S) (g : σ → S) (c : S) :
    MvPolynomial.eval₂ f (fun i => c * g i) φ = c ^ e * MvPolynomial.eval₂ f g φ := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = e := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hφ.coeff_eq_zero (by simpa [Finsupp.degree] using hne))
  have hpow : ∏ i ∈ d.support, (c * g i) ^ d i = c ^ e * ∏ i ∈ d.support, g i ^ d i := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  rw [hpow]; ring

/-- Homogeneous variable scaling, `eval₂Hom` form. -/
theorem isHomogeneous_eval₂Hom_scale {σ : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
    {e : ℕ} {φ : MvPolynomial σ R} (hφ : φ.IsHomogeneous e) (f : R →+* S) (g : σ → S) (c : S) :
    MvPolynomial.eval₂Hom f (fun i => c * g i) φ = c ^ e * MvPolynomial.eval₂Hom f g φ := by
  simp only [MvPolynomial.coe_eval₂Hom]
  exact isHomogeneous_eval₂_scale hφ f g c

/-- Homogeneous variable scaling, `bind₁` form. -/
theorem isHomogeneous_bind₁_scale {σ : Type*} {R : Type*} [CommSemiring R]
    {e : ℕ} {φ : MvPolynomial σ R} (hφ : φ.IsHomogeneous e)
    (g : σ → MvPolynomial σ R) (c : R) :
    bind₁ (fun i => MvPolynomial.C c * g i) φ = MvPolynomial.C c ^ e * bind₁ g φ := by
  show MvPolynomial.aeval (fun i => MvPolynomial.C c * g i) φ = _
  rw [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
    isHomogeneous_eval₂_scale hφ MvPolynomial.C g (MvPolynomial.C c)]
  show _ = MvPolynomial.C c ^ e * MvPolynomial.aeval g φ
  rw [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]

/-- `map` commutes with `homogeneousComponent`: both act coefficient-wise, degree by degree. -/
theorem map_homogeneousComponent {σ : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (n : ℕ) (φ : MvPolynomial σ R) :
    MvPolynomial.map f (MvPolynomial.homogeneousComponent n φ)
      = MvPolynomial.homogeneousComponent n (MvPolynomial.map f φ) := by
  ext d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent,
    MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_map]
  split <;> simp

/-- The homogeneous decomposition summed over any range past the total degree recovers the
polynomial. -/
theorem sum_homogeneousComponent_of_le {σ : Type*} {R : Type*} [CommSemiring R]
    {φ : MvPolynomial σ R} {N : ℕ} (h : φ.totalDegree ≤ N) :
    ∑ e ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent e φ = φ := by
  have hsub : Finset.range (φ.totalDegree + 1) ⊆ Finset.range (N + 1) := by
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent φ]
  refine (Finset.sum_subset hsub ?_).symm
  intro e _ hne
  refine MvPolynomial.homogeneousComponent_eq_zero e φ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hne
  exact hne

/-- General jet evaluation of a reshaped differential polynomial: the point sits in slot zero, the
jet variables carry an arbitrary jet vector. -/
theorem eval₂Hom_reshapeJet (n : ℕ) (z : ℂ) (jets : Fin (n + 1) → ℂ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) jets (reshapeJet n P)
      = MvPolynomial.eval (Fin.cons z jets) P := by
  have hhom : (MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) jets).comp (reshapeJet n)
      = (MvPolynomial.eval (Fin.cons z jets) : _ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [reshapeJet]
    · intro i
      induction i using Fin.cases with
      | zero => simp [reshapeJet]
      | succ j => simp [reshapeJet, Fin.cons_succ]
  exact RingHom.congr_fun hhom P

/-! ## The rational carrier -/

/-- **A digamma carrier whose off-pole jets are rational is hypertranscendental.**  If `M ≠ 0`,
`B ≠ 0`, and `F` has off-pole jets `F⁽ʲ⁾(z) = M·ψ⁽ʲ⁾(z) + C_j(z)/B(z)^{j+1}` for polynomials `C_j`,
then `F` satisfies no algebraic differential equation.  The general criterion behind the rational
carrier and the shift-orbit digamma carrier `∑ₖ mₖ ψ(·+nₖ)`. -/
theorem hypertranscendental_digamma_plus_offpole_rational {M : ℂ} (hM : M ≠ 0)
    (F : ℂ → ℂ) (B : Polynomial ℂ) (hB : B ≠ 0) (CCf : ℕ → Polynomial ℂ)
    (hjet : ∀ (j : ℕ) (z : ℂ), (∀ p : ℕ, z ≠ -(p : ℂ)) → B.eval z ≠ 0 →
      iteratedDeriv j F z
        = M * iteratedDeriv j Complex.digamma z + (CCf j).eval z / B.eval z ^ (j + 1)) :
    Hypertranscendental F := by
  rintro ⟨n, Q, hQ0, hQz⟩
  classical
  set f : ℂ → ℂ := F with hf
  set DD : Fin (n + 1) → Polynomial ℂ := fun i => CCf (i : ℕ) * B ^ (n - (i : ℕ)) with hDD
  set Qt : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) := reshapeJet n Q with hQt
  have hQt0 : Qt ≠ 0 := fun h0 => hQ0 (reshapeJet_injective n (by rw [← hQt, h0, map_zero]))
  set h : ℕ := Qt.totalDegree with hh
  set σ : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
    fun i => MvPolynomial.C (Polynomial.C M * B ^ (n + 1)) * MvPolynomial.X i
      + MvPolynomial.C (DD i) with hσ
  set P : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
    ∑ e ∈ Finset.range (h + 1),
      MvPolynomial.C (B ^ ((n + 1) * (h - e))) * bind₁ σ (homogeneousComponent e Qt) with hP
  -- the scaled-jet identity, off the zeros of `B` and the poles of `ψ`
  have hscaled : ∀ (z : ℂ), (∀ p : ℕ, z ≠ -(p : ℂ)) → B.eval z ≠ 0 → ∀ i : Fin (n + 1),
      (Polynomial.C M * B ^ (n + 1)).eval z * iteratedDeriv (i : ℕ) Complex.digamma z
          + (DD i).eval z
        = B.eval z ^ (n + 1) * iteratedDeriv (i : ℕ) f z := by
    intro z hz hBz i
    have hile : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.2
    have hpowsplit : B.eval z ^ (n + 1) = B.eval z ^ ((i : ℕ) + 1) * B.eval z ^ (n - (i : ℕ)) := by
      rw [← pow_add]; congr 1; omega
    rw [hjet (i : ℕ) z hz hBz, hDD]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rw [hpowsplit]
    field_simp
  -- ANNIHILATION of the digamma jets off every pole, via the `B` factor
  have hann : MvPolynomial.C B * P = 0 := by
    apply polyJetEval_offPole_eq_zero
    intro z hz
    rw [map_mul, polyJetEval_C]
    by_cases hBz : B.eval z = 0
    · rw [hBz, zero_mul]
    · have hfjet : ∀ e ∈ Finset.range (h + 1),
          polyJetEval (n + 1) z
              (MvPolynomial.C (B ^ ((n + 1) * (h - e))) * bind₁ σ (homogeneousComponent e Qt))
            = B.eval z ^ ((n + 1) * h)
              * MvPolynomial.eval₂Hom (Polynomial.evalRingHom z)
                  (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) (homogeneousComponent e Qt) := by
        intro e he
        have hle : e ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
        have hkey : (fun i => MvPolynomial.eval₂Hom (Polynomial.evalRingHom z)
              (digammaJet (n + 1) z) (σ i))
            = fun i : Fin (n + 1) => B.eval z ^ (n + 1) * iteratedDeriv (i : ℕ) f z := by
          funext i
          rw [hσ, map_add, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
            MvPolynomial.eval₂Hom_C]
          simp only [digammaJet]
          exact hscaled z hz hBz i
        rw [map_mul, polyJetEval_C]
        have hbind : polyJetEval (n + 1) z (bind₁ σ (homogeneousComponent e Qt))
            = B.eval z ^ ((n + 1) * e)
              * MvPolynomial.eval₂Hom (Polynomial.evalRingHom z)
                  (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) (homogeneousComponent e Qt) := by
          simp only [polyJetEval]
          rw [MvPolynomial.eval₂Hom_bind₁, hkey,
            isHomogeneous_eval₂Hom_scale (homogeneousComponent_isHomogeneous e Qt)
              (Polynomial.evalRingHom z) (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
              (B.eval z ^ (n + 1)), ← pow_mul]
        rw [hbind, Polynomial.eval_pow, ← mul_assoc, ← pow_add]
        congr 2
        rw [← Nat.mul_add, Nat.sub_add_cancel hle]
      rw [hP, map_sum, Finset.sum_congr rfl hfjet, ← Finset.mul_sum, ← map_sum]
      have hsum : (∑ e ∈ Finset.range (h + 1), homogeneousComponent e Qt) = Qt := by
        rw [hh]; exact MvPolynomial.sum_homogeneousComponent Qt
      rw [hsum, hQt, eval₂Hom_reshapeJet, hQz z, mul_zero, mul_zero]
  have hP0 : P = 0 := by
    have hCB : MvPolynomial.C B ≠ (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) := by
      simpa using hB
    rcases mul_eq_zero.mp hann with hbad | hgood
    · exact absurd hbad hCB
    · exact hgood
  -- NONZERO: over `RatFunc ℂ` the substitution is an affine isomorphism
  set am : Polynomial ℂ →+* RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) with ham
  set Φ : MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+* MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
    MvPolynomial.map am with hΦ
  have hamB : am B ≠ 0 := fun h0 => hB (RatFunc.algebraMap_injective ℂ (by rw [← ham, h0, map_zero]))
  have hbne : am B ^ (n + 1) ≠ 0 := pow_ne_zero _ hamB
  set MR : RatFunc ℂ := am (Polynomial.C M) with hMR
  have hMRne : MR ≠ 0 := fun h0 =>
    (Polynomial.C_ne_zero.mpr hM) (RatFunc.algebraMap_injective ℂ (by rw [← ham, ← hMR, h0, map_zero]))
  set ρ : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
    fun i => MvPolynomial.C MR * MvPolynomial.X i
      + MvPolynomial.C (am (DD i) / am B ^ (n + 1)) with hρ
  set ρ' : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
    fun i => MvPolynomial.C MR⁻¹ * MvPolynomial.X i
      - MvPolynomial.C (MR⁻¹ * (am (DD i) / am B ^ (n + 1))) with hρ'
  have hρinv : (fun i => bind₁ ρ' (ρ i))
      = (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (RatFunc ℂ)) := by
    funext i
    simp only [hρ, map_add, map_mul, bind₁_C_right, bind₁_X_right, hρ']
    have hMM : MvPolynomial.C MR * MvPolynomial.C MR⁻¹
        = (1 : MvPolynomial (Fin (n + 1)) (RatFunc ℂ)) := by
      rw [← map_mul, mul_inv_cancel₀ hMRne, map_one]
    linear_combination (MvPolynomial.X i
      - MvPolynomial.C (am (DD i) / am B ^ (n + 1))) * hMM
  have hbindρ_inj : Function.Injective (⇑(bind₁ ρ :
      MvPolynomial (Fin (n + 1)) (RatFunc ℂ) →ₐ[RatFunc ℂ] _)) := by
    have hcomp : (bind₁ ρ').comp (bind₁ ρ) = AlgHom.id (RatFunc ℂ) _ := by
      rw [bind₁_comp_bind₁, hρinv, bind₁_X_left]
    intro a b hab
    have hbb := congrArg (bind₁ ρ') hab
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hcomp, AlgHom.id_apply, AlgHom.id_apply] at hbb
    exact hbb
  have hΦQt : Φ Qt ≠ 0 := fun h0 =>
    hQt0 (MvPolynomial.map_injective am (RatFunc.algebraMap_injective ℂ) (by rw [← hΦ, h0, map_zero]))
  have hΦσ : ∀ i, Φ (σ i) = MvPolynomial.C (am B ^ (n + 1)) * ρ i := by
    intro i
    have e1 : am (Polynomial.C M) * am (B ^ (n + 1)) = am B ^ (n + 1) * MR := by
      rw [hMR, map_pow]; ring
    have e2 : am B ^ (n + 1) * (am (DD i) / am B ^ (n + 1)) = am (DD i) := by
      field_simp
    rw [hΦ, hσ]
    simp only [map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
    rw [← MvPolynomial.C_mul, e1, hρ, mul_add, ← mul_assoc, ← MvPolynomial.C_mul,
      ← MvPolynomial.C_mul, e2]
  have hmapP : Φ P = MvPolynomial.C (am B ^ ((n + 1) * h)) * bind₁ ρ (Φ Qt) := by
    rw [hP, map_sum]
    have hterm : ∀ e ∈ Finset.range (h + 1),
        Φ (MvPolynomial.C (B ^ ((n + 1) * (h - e))) * bind₁ σ (homogeneousComponent e Qt))
          = MvPolynomial.C (am B ^ ((n + 1) * h))
            * bind₁ ρ (homogeneousComponent e (Φ Qt)) := by
      intro e he
      have hle : e ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
      rw [hΦ, map_mul, MvPolynomial.map_C, map_pow, MvPolynomial.map_bind₁]
      rw [show (fun i => MvPolynomial.map am (σ i))
          = fun i => MvPolynomial.C (am B ^ (n + 1)) * ρ i
          from funext (fun i => by rw [← hΦ]; exact hΦσ i)]
      rw [map_homogeneousComponent, ← hΦ,
        isHomogeneous_bind₁_scale (homogeneousComponent_isHomogeneous e (Φ Qt)) ρ
          (am B ^ (n + 1))]
      rw [← MvPolynomial.C_pow, ← mul_assoc, ← MvPolynomial.C_mul, ← pow_mul, ← pow_add]
      congr 2
      rw [← Nat.mul_add, Nat.sub_add_cancel hle]
    have htd : (Φ Qt).totalDegree ≤ h := by
      rw [hh, hΦ]
      simp only [MvPolynomial.totalDegree]
      exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum,
      sum_homogeneousComponent_of_le htd]
  have hPne : P ≠ 0 := by
    intro hP0'
    have hz0 : Φ P = 0 := by rw [hP0', map_zero]
    rw [hmapP] at hz0
    rcases mul_eq_zero.mp hz0 with hc | hb
    · exact absurd (MvPolynomial.C_eq_zero.mp hc) (pow_ne_zero _ hamB)
    · exact hΦQt (hbindρ_inj (by rw [hb, map_zero]))
  exact hPne hP0

/-- **The digamma carrier plus a rational function is hypertranscendental.**  `M·ψ(t) + A(t)/B(t)`
satisfies no algebraic differential equation when `M ≠ 0` and `B ≠ 0`.  The off-pole jets are
`M·ψ⁽ʲ⁾ + (A/B)⁽ʲ⁾`, and `(A/B)⁽ʲ⁾ = C_j/B^{j+1}` by `exists_poly_iteratedDeriv_ratEval`. -/
theorem hypertranscendental_smul_digamma_add_ratfunc {M : ℂ} (hM : M ≠ 0)
    (A B : Polynomial ℂ) (hB : B ≠ 0) :
    Hypertranscendental (fun t => M * Complex.digamma t + A.eval t / B.eval t) := by
  refine hypertranscendental_digamma_plus_offpole_rational hM _ B hB
    (fun j => (exists_poly_iteratedDeriv_ratEval A B j).choose) ?_
  intro j z hz hBz
  have hψ : ContDiffAt ℂ j Complex.digamma z := contDiffAt_digamma_n z hz j
  have hAcont : ContDiffAt ℂ j (fun w => A.eval w) z := by
    have hc := (Polynomial.contDiff_aeval A (j : WithTop ℕ∞)).contDiffAt (x := z)
    have hfe : (fun x : ℂ => A.aeval x) = fun x : ℂ => A.eval x :=
      funext fun x => congrFun (Polynomial.coe_aeval_eq_eval x) A
    rwa [hfe] at hc
  have hBcont : ContDiffAt ℂ j (fun w => B.eval w) z := by
    have hc := (Polynomial.contDiff_aeval B (j : WithTop ℕ∞)).contDiffAt (x := z)
    have hfe : (fun x : ℂ => B.aeval x) = fun x : ℂ => B.eval x :=
      funext fun x => congrFun (Polynomial.coe_aeval_eq_eval x) B
    rwa [hfe] at hc
  have hABcont : ContDiffAt ℂ j (fun w => A.eval w / B.eval w) z := hAcont.div hBcont hBz
  rw [show (fun t => M * Complex.digamma t + A.eval t / B.eval t)
        = (fun t => M * Complex.digamma t) + (fun w => A.eval w / B.eval w) from rfl,
    iteratedDeriv_add (contDiffAt_const.mul hψ) hABcont, iteratedDeriv_const_mul M hψ,
    (exists_poly_iteratedDeriv_ratEval A B j).choose_spec z hBz]

end GaloisForLFunctions

end
