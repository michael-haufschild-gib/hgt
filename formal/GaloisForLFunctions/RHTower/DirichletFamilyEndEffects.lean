import GaloisForLFunctions.RHTower.DirichletFamilyBilinearForms
import Zeta23.PrimeSideA.Ends

/-!
# End effects averaged over the Dirichlet characters modulo `q`

In Alpöge–Furman's two-thirds argument the end-effect lemma compares the Frobenius norm of the
Gram matrix with the bilinear form `𝓜`:
`E(ν, ν) = L⁻² ∑_{k,l<d} G_{kl}(ν)² − 𝓜[ν, ν] = O(L l log l · B²)`, where `|ν(τ)| ≤ B + log⁺(|τ|/4T)`.
For the prime polynomial of one character `B ≍ √X`, so the error is linear in the polynomial
length `X`.  Averaged over the characters modulo `q` this is replaced by the residue-class sizes
`A_r = ∑_{n ≤ X, n ≡ r} a_n`:

`|∑_χ E(μ + P_χ, μ + P_χ)| ≤ C L l log l · φ(q) (B_μ² + (B_μ + A₁)² + (2π²)⁻¹ ∑_r (2(l + A_r)² + (l + A_r + A_{r⁻¹})²))`

(`abs_sum_endForm_dirichlet_le`).  The proof writes the character average of the bilinear form
`E` through residue-class polynomials (`sum_bilin_PXc_dirichlet`), polarises the cross terms, and
applies the single-density end-effect bound to each class polynomial.
-/

open MeasureTheory

noncomputable section

namespace RHTower

open Zeta23 Zeta23.PrimeSide Zeta23.ThmE

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- The end-effect form `E(u, v) = L⁻² ∑_{k,l<d} G_{kl}(u) G_{kl}(v) − 𝓜[u, v]`. -/
def endForm (p : Setting) (F : LocalFun) (u v : ℝ → ℝ) : ℝ :=
  (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu u p F k l * GentryNu v p F k l
    - Mform F.Phi p.T u v

lemma endForm_self (ν : ℝ → ℝ) :
    endForm p F ν ν
      = (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F := by
  unfold endForm MtotalNu
  simp only [sq]

lemma endForm_comm (hF : LocalHypsCoreW cϱ p F) (u v : ℝ → ℝ) :
    endForm p F u v = endForm p F v u := by
  unfold endForm
  rw [Mform_comm hF.Phi_even u v]
  congr 2
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma nuBound_of_abs_le {ν : ℝ → ℝ} {B : ℝ} (h : ∀ τ, |ν τ| ≤ B) : NuBound p B ν :=
  fun τ => (h τ).trans (le_add_of_nonneg_right (le_max_right _ _))

/-! ## Linearity -/

lemma gkl_integrable_of_abs_le (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) {u : ℝ → ℝ}
    (hu : Continuous u) {A : ℝ} (hA : 0 ≤ A) (huA : ∀ τ, |u τ| ≤ A) (k l : ℤ) :
    Integrable (gkl p F u k l) :=
  gkl_integrable hu hF (nuBound_of_abs_le huA) hT hA k l

lemma GentryNu_add (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {Bu Bv : ℝ} (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv)
    (hνu : NuBound p Bu u) (hνv : NuBound p Bv v) (k l : ℤ) :
    GentryNu (u + v) p F k l = GentryNu u p F k l + GentryNu v p F k l := by
  simp only [GentryNu_eq]
  rw [← integral_add (gkl_integrable hu hF hνu hT hBu k l) (gkl_integrable hv hF hνv hT hBv k l)]
  congr 1; funext τ; unfold gkl; simp only [Pi.add_apply]; ring

lemma GentryNu_neg (u : ℝ → ℝ) (k l : ℤ) :
    GentryNu (-u) p F k l = -GentryNu u p F k l := by
  simp only [GentryNu_eq]
  rw [← integral_neg]
  congr 1; funext τ; unfold gkl; simp only [Pi.neg_apply]; ring

lemma isTrigLinear_GentryNu (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) (R : Finset ℕ)
    (k l : ℤ) : IsTrigLinear (fun u => GentryNu u p F k l) R := by
  intro x x'
  have hc : ∀ n, Integrable (gkl p F (cosFreq n) k l) := fun n =>
    gkl_integrable_of_abs_le hF hT (continuous_cosFreq n) zero_le_one
      (fun τ => Real.abs_cos_le_one _) k l
  have hs : ∀ n, Integrable (gkl p F (sinFreq n) k l) := fun n =>
    gkl_integrable_of_abs_le hF hT (continuous_sinFreq n) zero_le_one
      (fun τ => Real.abs_sin_le_one _) k l
  have hpt : ∀ τ, gkl p F (trigPoly R x x') k l τ
      = ∑ n ∈ R, (x n * gkl p F (cosFreq n) k l τ + x' n * gkl p F (sinFreq n) k l τ) := by
    intro τ
    unfold gkl trigPoly cosFreq sinFreq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp only [GentryNu_eq]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_add, integral_const_mul, integral_const_mul]
    · exact (hc n).const_mul _
    · exact (hs n).const_mul _
  · intro n _
    exact ((hc n).const_mul _).add ((hs n).const_mul _)

lemma isTrigLinear_Mform_left {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (T : ℝ) {u : ℝ → ℝ}
    (hu : Continuous u) (R : Finset ℕ) : IsTrigLinear (fun v => Mform Φ T u v) R := by
  intro y y'
  have hint : ∀ v : ℝ → ℝ, Continuous v →
      Integrable (fun q : ℝ × ℝ => Φ (q.1 - q.2) ^ 2 * u q.1 * v q.2)
        (volume.restrict (Set.Icc T (2 * T) ×ˢ Set.Icc T (2 * T))) := fun v hv =>
    Mform_integrableOn hΦ hu hv
  have hpt : ∀ q : ℝ × ℝ, Φ (q.1 - q.2) ^ 2 * u q.1 * trigPoly R y y' q.2
      = ∑ m ∈ R, (y m * (Φ (q.1 - q.2) ^ 2 * u q.1 * cosFreq m q.2)
          + y' m * (Φ (q.1 - q.2) ^ 2 * u q.1 * sinFreq m q.2)) := by
    intro q
    unfold trigPoly cosFreq sinFreq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  unfold Mform
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_add, integral_const_mul, integral_const_mul]
    · exact (hint _ (continuous_cosFreq m)).const_mul _
    · exact (hint _ (continuous_sinFreq m)).const_mul _
  · intro m _
    exact ((hint _ (continuous_cosFreq m)).const_mul _).add
      ((hint _ (continuous_sinFreq m)).const_mul _)

/-- `E` is bilinear on trigonometric polynomials. -/
lemma isTrigBilin_endForm (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) (R : Finset ℕ) :
    IsTrigBilin (endForm p F) R :=
  ((IsTrigBilin.sum (Finset.univ : Finset (Fin p.d)) fun k _ =>
      IsTrigBilin.sum (Finset.univ : Finset (Fin p.d)) fun l _ =>
        isTrigBilin_mul (isTrigLinear_GentryNu hF hT R (k : ℤ) (l : ℤ))
          (isTrigLinear_GentryNu hF hT R (k : ℤ) (l : ℤ))).const_mul ((p.L)⁻¹ ^ 2)).sub
    (isTrigBilin_Mform hF.Phi_contDiff.continuous p.T R)

/-- For fixed continuous `u` with a density bound, `v ↦ E(u, v)` is linear on trigonometric
polynomials. -/
lemma isTrigLinear_endForm_left (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) (R : Finset ℕ)
    {u : ℝ → ℝ} (hu : Continuous u) : IsTrigLinear (fun v => endForm p F u v) R := by
  intro y y'
  have hG : ∀ k l : Fin p.d, GentryNu (trigPoly R y y') p F k l
      = ∑ m ∈ R, (y m * GentryNu (cosFreq m) p F k l + y' m * GentryNu (sinFreq m) p F k l) :=
    fun k l => isTrigLinear_GentryNu hF hT R k l y y'
  have hswap : ∀ g : Fin p.d → Fin p.d → ℕ → ℝ,
      ∑ k : Fin p.d, ∑ l : Fin p.d, ∑ m ∈ R, g k l m = ∑ m ∈ R, ∑ k : Fin p.d, ∑ l : Fin p.d, g k l m := by
    intro g
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm, Finset.sum_comm]
  have hM := isTrigLinear_Mform_left hF.Phi_contDiff.continuous p.T hu R y y'
  simp only at hM
  unfold endForm
  beta_reduce
  rw [hM]
  simp_rw [hG, Finset.mul_sum]
  rw [hswap (fun k l m => (p.L)⁻¹ ^ 2 * (GentryNu u p F k l
      * (y m * GentryNu (cosFreq m) p F k l + y' m * GentryNu (sinFreq m) p F k l))),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e1 : ∀ k l : Fin p.d, (p.L)⁻¹ ^ 2 * (GentryNu u p F k l
        * (y m * GentryNu (cosFreq m) p F k l + y' m * GentryNu (sinFreq m) p F k l))
      = y m * ((p.L)⁻¹ ^ 2 * (GentryNu u p F k l * GentryNu (cosFreq m) p F k l))
        + y' m * ((p.L)⁻¹ ^ 2 * (GentryNu u p F k l * GentryNu (sinFreq m) p F k l)) :=
    fun k l => by ring
  simp_rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-! ## Additivity including the archimedean density -/

lemma Mform_neg_right {Φ : ℝ → ℝ} {T : ℝ} (u v : ℝ → ℝ) :
    Mform Φ T u (-v) = -Mform Φ T u v := by
  have e : (-v) = fun x => (-1) * v x := by funext x; simp
  rw [e, Mform_const_mul_right]; ring

lemma Mform_neg_left {Φ : ℝ → ℝ} {T : ℝ} (u v : ℝ → ℝ) :
    Mform Φ T (-u) v = -Mform Φ T u v := by
  have e : (-u) = fun x => (-1) * u x := by funext x; simp
  rw [e, Mform_const_mul_left]; ring

lemma endForm_add_add (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {Bu Bv : ℝ} (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv)
    (hνu : NuBound p Bu u) (hνv : NuBound p Bv v) :
    endForm p F (u + v) (u + v)
      = endForm p F u u + endForm p F u v + endForm p F v u + endForm p F v v := by
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  unfold endForm
  simp_rw [GentryNu_add hF hT hu hv hBu hBv hνu hνv]
  rw [Mform_add_left hΦ hu hv (hu.add hv), Mform_add_right hΦ hu hv hu,
    Mform_add_right hΦ hu hv hv]
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

lemma endForm_sub_sub (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {Bu Bv : ℝ} (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv)
    (hνu : NuBound p Bu u) (hνv : NuBound p Bv v) :
    endForm p F (u - v) (u - v)
      = endForm p F u u - endForm p F u v - endForm p F v u + endForm p F v v := by
  have hνv' : NuBound p Bv (-v) := fun τ => by simpa using hνv τ
  rw [sub_eq_add_neg, endForm_add_add hF hT hu hv.neg hBu hBv hνu hνv']
  unfold endForm
  simp_rw [GentryNu_neg]
  rw [Mform_neg_right, Mform_neg_left, Mform_neg_left, Mform_neg_right]
  simp only [neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib]
  ring

/-! ## The end-effect bound for one density -/

/-- Zeta23's end-effect lemma, in the form `|E(ν, ν)| ≤ C L l log l B²`. -/
lemma exists_abs_endForm_self_le (cϱ lam : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      |endForm p F ν ν| ≤ C * (p.L * p.l * Real.log p.l * B ^ 2) := by
  obtain ⟨C, T₀, h⟩ := lem_ends_nu_W (cϱ := cϱ) (lam := lam)
  exact ⟨C, T₀, fun p F B ν hl hT hF hL hc hν hB => by
    rw [endForm_self]; exact h p F B ν hl hT hF hL hc hν hB⟩

/-! ## The character average -/

/-- `A_r = ∑_{n ≤ X, n ≡ r} a_n`. -/
def classMass (q : ℕ) (X : ℝ) (r : ZMod q) : ℝ := ∑ n ∈ primeRange X, classCoef q r n

open Classical in
/-- The coefficients of the character sum of the prime polynomials,
`(1/φ(q)) ∑_χ P_χ = −(1/π) ∑_{n ≤ X, n ≡ 1} a_n cos(τ log n)`. -/
def oneClassCoef (q : ℕ) (n : ℕ) : ℝ := -(1 / Real.pi) * acoef n * (if (n : ZMod q) = 1 then 1 else 0)

/-- `A₁ = (1/π) ∑_{n ≤ X, n ≡ 1} a_n`, the size of `(1/φ(q)) ∑_χ P_χ`. -/
def oneClassMass (q : ℕ) (X : ℝ) : ℝ := ∑ n ∈ primeRange X, |oneClassCoef q n|

lemma classCoef_nonneg (q : ℕ) (r : ZMod q) (n : ℕ) : 0 ≤ classCoef q r n := by
  unfold classCoef; split_ifs
  · exact acoef_nonneg n
  · exact le_rfl

lemma classMass_nonneg (q : ℕ) (X : ℝ) (r : ZMod q) : 0 ≤ classMass q X r :=
  Finset.sum_nonneg fun n _ => classCoef_nonneg q r n

lemma abs_trigPoly_class_le (q : ℕ) (X : ℝ) (r r' : ZMod q) (s : ℝ) (hs : |s| ≤ 1) (τ : ℝ) :
    |trigPoly (primeRange X) (classCoef q r + s • classCoef q r') 0 τ|
      ≤ classMass q X r + classMass q X r' := by
  refine (abs_trigPoly_le _ _ _ τ).trans ?_
  unfold classMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, abs_zero, add_zero]
  refine (abs_add_le _ _).trans (add_le_add (abs_of_nonneg (classCoef_nonneg q r n)).le ?_)
  rw [abs_mul, abs_of_nonneg (classCoef_nonneg q r' n)]
  exact mul_le_of_le_one_left (classCoef_nonneg q r' n) hs

lemma abs_trigPoly_class_sin_le (q : ℕ) (X : ℝ) (r r' : ZMod q) (s : ℝ) (hs : |s| ≤ 1) (τ : ℝ) :
    |trigPoly (primeRange X) 0 (classCoef q r + s • classCoef q r') τ|
      ≤ classMass q X r + classMass q X r' := by
  refine (abs_trigPoly_le _ _ _ τ).trans ?_
  unfold classMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, abs_zero, zero_add]
  refine (abs_add_le _ _).trans (add_le_add (abs_of_nonneg (classCoef_nonneg q r n)).le ?_)
  rw [abs_mul, abs_of_nonneg (classCoef_nonneg q r' n)]
  exact mul_le_of_le_one_left (classCoef_nonneg q r' n) hs

lemma abs_classCos_le (q : ℕ) (X : ℝ) (r : ZMod q) (τ : ℝ) :
    |classCos q X r τ| ≤ classMass q X r := by
  refine (abs_trigPoly_le _ _ _ τ).trans (le_of_eq ?_)
  unfold classMass
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [abs_of_nonneg (classCoef_nonneg q r n)]

lemma abs_classSin_le (q : ℕ) (X : ℝ) (r : ZMod q) (τ : ℝ) :
    |classSin q X r τ| ≤ classMass q X r := by
  refine (abs_trigPoly_le _ _ _ τ).trans (le_of_eq ?_)
  unfold classMass
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [abs_of_nonneg (classCoef_nonneg q r n)]

lemma sum_dirichletChar_re_apply {q : ℕ} [NeZero q] (n : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, (χ n).re
      = q.totient * (if (n : ZMod q) = 1 then (1 : ℝ) else 0) := by
  rw [← Complex.re_sum, DirichletCharacter.sum_characters_eq ℂ (n : ZMod q)]
  split_ifs <;> simp

lemma sum_dirichletChar_im_apply {q : ℕ} [NeZero q] (n : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, (χ n).im = 0 := by
  rw [← Complex.im_sum, DirichletCharacter.sum_characters_eq ℂ (n : ZMod q)]
  split_ifs <;> simp

lemma card_dirichletCharacter (q : ℕ) [NeZero q] :
    (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- **Family end effects.**  There are `C, T₀` (depending on `c_ϱ, λ`) such that for every
modulus `q`, every continuous archimedean density `μ` with `|μ(τ)| ≤ B_μ + log⁺(|τ|/4T)`,
`B_μ ≥ l`, and the window data of Alpöge–Furman at `T ≥ T₀` with `L ≤ 2l`,
`|∑_χ E(μ + P_χ, μ + P_χ)| ≤ C L l log l · φ(q) · (B_μ² + (B_μ + A₁)²
  + (2π²)⁻¹ ∑_{r unit} (2(l + A_r)² + (l + A_r + A_{r⁻¹})²))`. -/
theorem abs_sum_endForm_dirichlet_le (cϱ lam : ℝ) :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (q : ℕ) [NeZero q] (μ : ℝ → ℝ) (Bμ : ℝ),
      p.lam = lam → T₀ ≤ p.T → LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous μ →
      NuBound p Bμ μ → p.l ≤ Bμ →
      |∑ χ : DirichletCharacter ℂ q,
          endForm p F (μ + PXc (fun n => χ n) p.X) (μ + PXc (fun n => χ n) p.X)|
        ≤ C * (p.L * p.l * Real.log p.l) * q.totient *
          (Bμ ^ 2 + (Bμ + oneClassMass q p.X) ^ 2 + 1 / (2 * Real.pi ^ 2) *
            ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
              (2 * (p.l + classMass q p.X r) ^ 2
                + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2)) := by
  obtain ⟨C, T₀, hC⟩ := exists_abs_endForm_self_le cϱ lam
  refine ⟨C, max T₀ 1, fun p F q _ μ Bμ hl hT hF hL hμc hμ hBμ => ?_⟩
  classical
  have hT0 : T₀ ≤ p.T := le_trans (le_max_left _ _) hT
  have hT1 : 1 ≤ p.T := le_trans (le_max_right _ _) hT
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hBμ0 : 0 ≤ Bμ := by linarith
  set Λe : ℝ := C * (p.L * p.l * Real.log p.l) with hΛe
  set φq : ℝ := (q.totient : ℝ) with hφq
  set R := primeRange p.X with hR
  set U := (Finset.univ : Finset (ZMod q)).filter IsUnit with hU
  have hbound : ∀ (B : ℝ) (ν : ℝ → ℝ), Continuous ν → NuBound p B ν → p.l ≤ B →
      |endForm p F ν ν| ≤ Λe * B ^ 2 := fun B ν hc hν hB => by
    have := hC p F B ν hl hT0 hF hL hc hν hB
    rw [hΛe]; linarith
  have hBil := isTrigBilin_endForm hF hT1 R
  have hsymm : ∀ u v, endForm p F u v = endForm p F v u := endForm_comm hF
  -- the prime polynomials as trigonometric polynomials
  set xχ : DirichletCharacter ℂ q → ℕ → ℝ := fun χ n => -(1 / Real.pi) * acoef n * (χ n).re
    with hxχ
  set yχ : DirichletCharacter ℂ q → ℕ → ℝ := fun χ n => -(1 / Real.pi) * acoef n * (χ n).im
    with hyχ
  have hP : ∀ χ : DirichletCharacter ℂ q, PXc (fun n => χ n) p.X = trigPoly R (xχ χ) (yχ χ) :=
    fun χ => PXc_dirichlet_eq_trigPoly χ p.X
  have hPbd : ∀ χ : DirichletCharacter ℂ q, NuBound p (∑ n ∈ R, (|xχ χ n| + |yχ χ n|))
      (PXc (fun n => χ n) p.X) := fun χ => by
    rw [hP χ]; exact nuBound_of_abs_le (abs_trigPoly_le _ _ _)
  have hPB0 : ∀ χ : DirichletCharacter ℂ q, 0 ≤ ∑ n ∈ R, (|xχ χ n| + |yχ χ n|) :=
    fun χ => Finset.sum_nonneg fun n _ => by positivity
  -- step 1: expand each square
  have hexp : ∀ χ : DirichletCharacter ℂ q,
      endForm p F (μ + PXc (fun n => χ n) p.X) (μ + PXc (fun n => χ n) p.X)
        = endForm p F μ μ + 2 * endForm p F μ (PXc (fun n => χ n) p.X)
          + endForm p F (PXc (fun n => χ n) p.X) (PXc (fun n => χ n) p.X) := fun χ => by
    rw [endForm_add_add hF hT1 hμc (continuous_PXc _ _) hBμ0 (hPB0 χ) hμ (hPbd χ),
      hsymm (PXc (fun n => χ n) p.X) μ]
    ring
  -- step 2: the cross term averages to the class `1`
  set P1 : ℝ → ℝ := trigPoly R (oneClassCoef q) 0 with hP1
  have hcross : ∑ χ : DirichletCharacter ℂ q, endForm p F μ (PXc (fun n => χ n) p.X)
      = φq * endForm p F μ P1 := by
    have hlin := isTrigLinear_endForm_left hF hT1 R hμc
    simp only [IsTrigLinear] at hlin
    simp_rw [hP, hlin, hP1, hlin]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    simp only [hxχ, hyχ]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_dirichletChar_re_apply,
      sum_dirichletChar_im_apply]
    unfold oneClassCoef
    simp only [Pi.zero_apply]
    ring
  -- step 3: the prime part through residue classes
  have hpp := sum_bilin_PXc_dirichlet (q := q) p.X (endForm p F) hBil
  -- assemble the identity
  have hident : ∑ χ : DirichletCharacter ℂ q,
      endForm p F (μ + PXc (fun n => χ n) p.X) (μ + PXc (fun n => χ n) p.X)
        = φq * endForm p F μ μ + 2 * (φq * endForm p F μ P1)
          + φq / (2 * Real.pi ^ 2) * ∑ r ∈ U,
            (endForm p F (classCos q p.X r) (classCos q p.X r)
              + endForm p F (classSin q p.X r) (classSin q p.X r)
              + endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)
              - endForm p F (classSin q p.X r) (classSin q p.X r⁻¹)) := by
    rw [Finset.sum_congr rfl fun χ _ => hexp χ, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, card_dirichletCharacter, nsmul_eq_mul, ← Finset.mul_sum, hcross, hpp]
  -- bounds
  have hA1 : 0 ≤ oneClassMass q p.X := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hP1bd : NuBound p (oneClassMass q p.X) P1 := by
    refine nuBound_of_abs_le fun τ => (abs_trigPoly_le _ _ _ τ).trans (le_of_eq ?_)
    simp [oneClassMass, hR]
  have hb_μμ : |endForm p F μ μ| ≤ Λe * Bμ ^ 2 := hbound Bμ μ hμc hμ hBμ
  have hb_μP : |endForm p F μ P1| ≤ Λe * (Bμ + oneClassMass q p.X) ^ 2 / 2 := by
    have hP1c : Continuous P1 := continuous_trigPoly _ _ _
    have hplus : NuBound p (Bμ + oneClassMass q p.X) (μ + P1) := fun τ => by
      have h1 := hμ τ; have h2 := hP1bd τ
      have h3 : |P1 τ| ≤ oneClassMass q p.X := by
        have := (abs_trigPoly_le R (oneClassCoef q) 0 τ)
        refine this.trans (le_of_eq ?_); simp [oneClassMass, hR]
      simp only [Pi.add_apply]
      linarith [abs_add_le (μ τ) (P1 τ)]
    have hminus : NuBound p (Bμ + oneClassMass q p.X) (μ - P1) := fun τ => by
      have h1 := hμ τ
      have h3 : |P1 τ| ≤ oneClassMass q p.X := by
        have := (abs_trigPoly_le R (oneClassCoef q) 0 τ)
        refine this.trans (le_of_eq ?_); simp [oneClassMass, hR]
      simp only [Pi.sub_apply]
      linarith [abs_sub (μ τ) (P1 τ)]
    have hpol : 4 * endForm p F μ P1
        = endForm p F (μ + P1) (μ + P1) - endForm p F (μ - P1) (μ - P1) := by
      rw [endForm_add_add hF hT1 hμc hP1c hBμ0 hA1 hμ hP1bd,
        endForm_sub_sub hF hT1 hμc hP1c hBμ0 hA1 hμ hP1bd, hsymm P1 μ]
      ring
    have h1 := hbound _ _ (hμc.add hP1c) hplus (by linarith)
    have h2 := hbound _ _ (hμc.sub hP1c) hminus (by linarith)
    have : |4 * endForm p F μ P1| ≤ 2 * (Λe * (Bμ + oneClassMass q p.X) ^ 2) := by
      rw [hpol]; exact (abs_sub _ _).trans (by linarith)
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)] at this
    linarith
  have hb_class : ∀ r ∈ U,
      |endForm p F (classCos q p.X r) (classCos q p.X r)
        + endForm p F (classSin q p.X r) (classSin q p.X r)
        + endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)
        - endForm p F (classSin q p.X r) (classSin q p.X r⁻¹)|
      ≤ Λe * (2 * (p.l + classMass q p.X r) ^ 2
          + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2) := by
    intro r _
    have hAr := classMass_nonneg q p.X r
    have hAr' := classMass_nonneg q p.X r⁻¹
    -- the single class polynomials
    have hCbd : ∀ r' : ZMod q, NuBound p (p.l + classMass q p.X r') (classCos q p.X r') := by
      intro r'
      refine nuBound_of_abs_le fun τ => ?_
      have := abs_classCos_le q p.X r' τ
      linarith [classMass_nonneg q p.X r']
    have hSbd : ∀ r' : ZMod q, NuBound p (p.l + classMass q p.X r') (classSin q p.X r') := by
      intro r'
      refine nuBound_of_abs_le fun τ => ?_
      have := abs_classSin_le q p.X r' τ
      linarith [classMass_nonneg q p.X r']
    have hCC := hbound _ _ (continuous_trigPoly _ _ _) (hCbd r) (by linarith)
    have hSS := hbound _ _ (continuous_trigPoly _ _ _) (hSbd r) (by linarith)
    -- polarised cross terms
    have hpm : ∀ (s : ℝ), |s| ≤ 1 →
        NuBound p (p.l + classMass q p.X r + classMass q p.X r⁻¹)
          (trigPoly R (classCoef q r + s • classCoef q r⁻¹) 0) ∧
        NuBound p (p.l + classMass q p.X r + classMass q p.X r⁻¹)
          (trigPoly R 0 (classCoef q r + s • classCoef q r⁻¹)) := by
      intro s hs
      constructor
      · refine nuBound_of_abs_le fun τ => ?_
        have := abs_trigPoly_class_le q p.X r r⁻¹ s hs τ
        linarith
      · refine nuBound_of_abs_le fun τ => ?_
        have := abs_trigPoly_class_sin_le q p.X r r⁻¹ s hs τ
        linarith
    have hpolC := hBil.polarization hsymm (classCoef q r) 0 (classCoef q r⁻¹) 0
    have hpolS := hBil.polarization hsymm 0 (classCoef q r) 0 (classCoef q r⁻¹)
    have eadd : classCoef q r + classCoef q r⁻¹ = classCoef q r + (1 : ℝ) • classCoef q r⁻¹ := by
      rw [one_smul]
    have esub : classCoef q r - classCoef q r⁻¹ = classCoef q r + (-1 : ℝ) • classCoef q r⁻¹ := by
      rw [neg_one_smul, sub_eq_add_neg]
    have hz : (0 : ℕ → ℝ) + 0 = 0 := add_zero 0
    have hz' : (0 : ℕ → ℝ) - 0 = 0 := sub_zero 0
    rw [eadd, esub, hz, hz'] at hpolC
    rw [eadd, esub, hz, hz'] at hpolS
    have hB2 : p.l ≤ p.l + classMass q p.X r + classMass q p.X r⁻¹ := by linarith
    have c1 := hbound _ _ (continuous_trigPoly _ _ _) (hpm 1 (by norm_num)).1 hB2
    have c2 := hbound _ _ (continuous_trigPoly _ _ _) (hpm (-1) (by norm_num)).1 hB2
    have s1 := hbound _ _ (continuous_trigPoly _ _ _) (hpm 1 (by norm_num)).2 hB2
    have s2 := hbound _ _ (continuous_trigPoly _ _ _) (hpm (-1) (by norm_num)).2 hB2
    have hCr : |endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)|
        ≤ Λe * (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2 / 2 := by
      have : |4 * endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)|
          ≤ 2 * (Λe * (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2) := by
        unfold classCos; rw [hpolC]; exact (abs_sub _ _).trans (by linarith)
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)] at this
      linarith
    have hSr : |endForm p F (classSin q p.X r) (classSin q p.X r⁻¹)|
        ≤ Λe * (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2 / 2 := by
      have : |4 * endForm p F (classSin q p.X r) (classSin q p.X r⁻¹)|
          ≤ 2 * (Λe * (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2) := by
        unfold classSin; rw [hpolS]; exact (abs_sub _ _).trans (by linarith)
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)] at this
      linarith
    have t1 := abs_add_le (endForm p F (classCos q p.X r) (classCos q p.X r))
      (endForm p F (classSin q p.X r) (classSin q p.X r))
    have t2 := abs_add_le (endForm p F (classCos q p.X r) (classCos q p.X r)
      + endForm p F (classSin q p.X r) (classSin q p.X r))
      (endForm p F (classCos q p.X r) (classCos q p.X r⁻¹))
    have t3 := abs_sub (endForm p F (classCos q p.X r) (classCos q p.X r)
      + endForm p F (classSin q p.X r) (classSin q p.X r)
      + endForm p F (classCos q p.X r) (classCos q p.X r⁻¹))
      (endForm p F (classSin q p.X r) (classSin q p.X r⁻¹))
    set α := Λe * (p.l + classMass q p.X r) ^ 2 with hα
    set β := Λe * (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2 with hβ
    have hgoal : Λe * (2 * (p.l + classMass q p.X r) ^ 2
        + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2) = 2 * α + β := by
      rw [hα, hβ]; ring
    rw [hgoal]
    have hCr' : |endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)| ≤ β / 2 := by
      rw [hβ]; exact hCr
    have hSr' : |endForm p F (classSin q p.X r) (classSin q p.X r⁻¹)| ≤ β / 2 := by
      rw [hβ]; exact hSr
    have hCC' : |endForm p F (classCos q p.X r) (classCos q p.X r)| ≤ α := hCC
    have hSS' : |endForm p F (classSin q p.X r) (classSin q p.X r)| ≤ α := hSS
    calc _ ≤ _ := t3
      _ ≤ |endForm p F (classCos q p.X r) (classCos q p.X r)|
          + |endForm p F (classSin q p.X r) (classSin q p.X r)|
          + |endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)|
          + |endForm p F (classSin q p.X r) (classSin q p.X r⁻¹)| := by linarith
      _ ≤ α + α + β / 2 + β / 2 := by linarith
      _ = 2 * α + β := by ring
  have hφ0 : 0 ≤ φq := Nat.cast_nonneg _
  have hπ2 : 0 < 2 * Real.pi ^ 2 := by positivity
  rw [hident]
  have hsum : |∑ r ∈ U,
      (endForm p F (classCos q p.X r) (classCos q p.X r)
        + endForm p F (classSin q p.X r) (classSin q p.X r)
        + endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)
        - endForm p F (classSin q p.X r) (classSin q p.X r⁻¹))|
      ≤ Λe * ∑ r ∈ U, (2 * (p.l + classMass q p.X r) ^ 2
          + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2) := by
    rw [Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hb_class)
  have e1 : |φq * endForm p F μ μ| ≤ φq * (Λe * Bμ ^ 2) := by
    rw [abs_mul, abs_of_nonneg hφ0]; exact mul_le_mul_of_nonneg_left hb_μμ hφ0
  have e2 : |2 * (φq * endForm p F μ P1)| ≤ φq * (Λe * (Bμ + oneClassMass q p.X) ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hφ0, abs_two]
    nlinarith [mul_le_mul_of_nonneg_left hb_μP hφ0]
  have e3 : |φq / (2 * Real.pi ^ 2) * ∑ r ∈ U,
      (endForm p F (classCos q p.X r) (classCos q p.X r)
        + endForm p F (classSin q p.X r) (classSin q p.X r)
        + endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)
        - endForm p F (classSin q p.X r) (classSin q p.X r⁻¹))|
      ≤ φq / (2 * Real.pi ^ 2) * (Λe * ∑ r ∈ U, (2 * (p.l + classMass q p.X r) ^ 2
          + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2)) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  calc _ ≤ |φq * endForm p F μ μ + 2 * (φq * endForm p F μ P1)|
        + |φq / (2 * Real.pi ^ 2) * ∑ r ∈ U,
          (endForm p F (classCos q p.X r) (classCos q p.X r)
            + endForm p F (classSin q p.X r) (classSin q p.X r)
            + endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)
            - endForm p F (classSin q p.X r) (classSin q p.X r⁻¹))| := abs_add_le _ _
    _ ≤ |φq * endForm p F μ μ| + |2 * (φq * endForm p F μ P1)|
        + |φq / (2 * Real.pi ^ 2) * ∑ r ∈ U,
          (endForm p F (classCos q p.X r) (classCos q p.X r)
            + endForm p F (classSin q p.X r) (classSin q p.X r)
            + endForm p F (classCos q p.X r) (classCos q p.X r⁻¹)
            - endForm p F (classSin q p.X r) (classSin q p.X r⁻¹))| := by
        gcongr; exact abs_add_le _ _
    _ ≤ φq * (Λe * Bμ ^ 2) + φq * (Λe * (Bμ + oneClassMass q p.X) ^ 2)
        + φq / (2 * Real.pi ^ 2) * (Λe * ∑ r ∈ U, (2 * (p.l + classMass q p.X r) ^ 2
          + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2)) := by linarith
    _ = Λe * φq * (Bμ ^ 2 + (Bμ + oneClassMass q p.X) ^ 2 + 1 / (2 * Real.pi ^ 2) *
          ∑ r ∈ U, (2 * (p.l + classMass q p.X r) ^ 2
            + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2)) := by
        field_simp

end RHTower
