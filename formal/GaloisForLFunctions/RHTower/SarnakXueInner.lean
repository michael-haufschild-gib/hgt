import GaloisForLFunctions.RHTower.SarnakXueEigenspaceBound
import GaloisForLFunctions.RHTower.MaassCongruenceL2
import GaloisForLFunctions.RHTower.SelbergMaassEigenspaceQuotientL2
import GaloisForLFunctions.RHTower.HyperbolicPointPair

open MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups

/-!
# The coset-sum inner product on principal Maass eigenspaces

On the zero-inclusive principal eigenspace `V` (level `p = N + 1`, eigenvalue `λ`), the pairing
`⟨u, v⟩ = ∫_𝒟 Σ_{q ∈ SL(2,ℤ)/Γ(p)} conj(u(q̃z)) v(q̃z) dμ` over the modular cell `𝒟` is well defined (every
element is continuous and bounded), Hermitian, and positive definite: for `u ≠ 0` it is the positive
trace mass `∫_𝒟 density` (`ip_self_pos`). It is an `InnerProductSpace.Core` on every subspace (`core`).
For any inner product space, `|φ v|² ≤ M ‖v‖²` for a linear functional forces `Σ_i |φ(b_i)|² ≤ M` on
every orthonormal basis (`sum_normSq_le`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXueInner

open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace
open GaloisForLFunctions.RHTower.MaassCongruenceL2

noncomputable section

variable (N : ℕ) (lam : ℝ)

abbrev V := glMaassCuspEigenspace (principalCongruenceGL N) lam

theorem toMaass_apply (u : V N lam) (hu : u ≠ 0) (z : ℍ) :
    (PrincipalMaassEigenspaceL2.toMaassCuspEigenform N u hu).1.1 z = u.1 z := rfl

variable {N lam}

theorem continuous_sl_smul (A : SL(2, ℤ)) : Continuous (fun z : ℍ => A • z) := by
  show Continuous (fun z : ℍ => (A : GL (Fin 2) ℝ) • z)
  exact continuous_const_smul _

theorem V_continuous (u : V N lam) : Continuous u.1 :=
  HyperbolicPointPair.continuous_of_smooth u.2.2.1.1

theorem V_bounded (u : V N lam) : ∃ C : ℝ, ∀ z, ‖u.1 z‖ ≤ C := by
  by_cases hu : u = 0
  · exact ⟨0, fun z => by simp [hu]⟩
  · obtain ⟨C, hC⟩ := source_bounded N (PrincipalMaassEigenspaceL2.toMaassCuspEigenform N u hu)
    exact ⟨C, fun z => by simpa [toMaass_apply] using hC z⟩

/-- The integrand of the coset-sum inner product. -/
def ipDensity (u v : V N lam) (z : ℍ) : ℂ :=
  ∑ q : Deck N, (starRingEnd ℂ) (u.1 (q.out • z)) * v.1 (q.out • z)

theorem ipDensity_continuous (u v : V N lam) : Continuous (ipDensity u v) := by
  unfold ipDensity
  refine continuous_finsetSum _ (fun q _ => ?_)
  exact (Complex.continuous_conj.comp ((V_continuous u).comp (continuous_sl_smul _))).mul
    ((V_continuous v).comp (continuous_sl_smul _))

theorem ipDensity_integrable (u v : V N lam) : Integrable (ipDensity u v) cellMeasure := by
  obtain ⟨Cu, hCu⟩ := V_bounded u
  obtain ⟨Cv, hCv⟩ := V_bounded v
  refine (MemLp.of_bound (p := 1) (ipDensity_continuous u v).aestronglyMeasurable
    (Fintype.card (Deck N) * (Cu * Cv)) (ae_of_all _ (fun z => ?_))).integrable (by simp)
  unfold ipDensity
  calc ‖∑ q : Deck N, (starRingEnd ℂ) (u.1 (q.out • z)) * v.1 (q.out • z)‖
      ≤ ∑ q : Deck N, ‖(starRingEnd ℂ) (u.1 (q.out • z)) * v.1 (q.out • z)‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Deck N, Cu * Cv := by
        apply Finset.sum_le_sum
        intro q _
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (hCu _) (hCv _) (norm_nonneg _) ((norm_nonneg _).trans (hCu z))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The coset-sum inner product `⟨u, v⟩ = ∫_𝒟 Σ_q conj(u(q̃z)) v(q̃z) dμ`. -/
def ip (u v : V N lam) : ℂ := ∫ z, ipDensity u v z ∂cellMeasure

theorem ipDensity_self (u : V N lam) (z : ℍ) :
    ipDensity u u z = ((∑ q : Deck N, Complex.normSq (u.1 (q.out • z)) : ℝ) : ℂ) := by
  unfold ipDensity
  push_cast
  apply Finset.sum_congr rfl
  intro q _
  rw [Complex.normSq_eq_conj_mul_self]

theorem ip_self (u : V N lam) :
    ip u u = ((∫ z, ∑ q : Deck N, Complex.normSq (u.1 (q.out • z)) ∂cellMeasure : ℝ) : ℂ) := by
  unfold ip
  simp_rw [ipDensity_self]
  exact integral_ofReal


open SelbergMaassCuspTransport in
theorem density_eq (u : V N lam) (hu : u ≠ 0) (z : ℍ) :
    density N (PrincipalMaassEigenspaceL2.toMaassCuspEigenform N u hu) z =
      ∑ q : Deck N, Complex.normSq (u.1 (q.out • z)) := by
  unfold density
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [quotientForm_mk, translate_apply]
  rfl

theorem ip_self_pos (u : V N lam) (hu : u ≠ 0) : 0 < (ip u u).re := by
  rw [ip_self, Complex.ofReal_re]
  have := source_mass_pos N (PrincipalMaassEigenspaceL2.toMaassCuspEigenform N u hu)
  simp_rw [density_eq u hu] at this
  exact this

theorem ip_self_re_nonneg (u : V N lam) : 0 ≤ (ip u u).re := by
  rw [ip_self, Complex.ofReal_re]
  exact integral_nonneg (fun z => Finset.sum_nonneg (fun q _ => Complex.normSq_nonneg _))

theorem ip_conj (u v : V N lam) : (starRingEnd ℂ) (ip v u) = ip u v := by
  unfold ip
  rw [← integral_conj]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [ipDensity, map_sum, map_mul, Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem ip_add_left (u u' v : V N lam) : ip (u + u') v = ip u v + ip u' v := by
  unfold ip
  rw [← integral_add (ipDensity_integrable u v) (ipDensity_integrable u' v)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [ipDensity, Submodule.coe_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem ip_smul_left (r : ℂ) (u v : V N lam) : ip (r • u) v = (starRingEnd ℂ) r * ip u v := by
  unfold ip
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  simp only [ipDensity, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The coset-sum inner product on any subspace of the principal eigenspace. -/
@[reducible] def core (W : Submodule ℂ (V N lam)) : InnerProductSpace.Core ℂ W where
  inner u v := ip u.1 v.1
  conj_inner_symm u v := ip_conj u.1 v.1
  re_inner_nonneg u := ip_self_re_nonneg u.1
  add_left u u' v := ip_add_left u.1 u'.1 v.1
  smul_left u v r := ip_smul_left r u.1 v.1
  definite u h := by
    by_contra hne
    have hu : u.1 ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have := ip_self_pos u.1 hu
    have h' : ip u.1 u.1 = 0 := h
    rw [h', Complex.zero_re] at this
    exact lt_irrefl 0 this

end

section ONB
open scoped InnerProductSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]

/-- If a linear functional satisfies `|φ v|² ≤ M ‖v‖²`, then `Σ |φ(b_i)|² ≤ M` for every orthonormal
basis `b`: test the bound on `e = Σ conj(φ b_i) b_i`, for which `φ e = ‖e‖² = Σ |φ b_i|²`. -/
theorem sum_normSq_le (b : OrthonormalBasis ι ℂ E) (φ : E →ₗ[ℂ] ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ v, Complex.normSq (φ v) ≤ M * ‖v‖ ^ 2) :
    ∑ i, Complex.normSq (φ (b i)) ≤ M := by
  set S := ∑ i, Complex.normSq (φ (b i))
  set e : E := ∑ i, (starRingEnd ℂ) (φ (b i)) • b i
  have hφe : φ e = (S : ℂ) := by
    simp only [e, map_sum, map_smul, smul_eq_mul, S]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.normSq_eq_conj_mul_self]
  have hne : ‖e‖ ^ 2 = S := by
    have h1 := b.orthonormal.inner_sum (fun i => (starRingEnd ℂ) (φ (b i)))
      (fun i => (starRingEnd ℂ) (φ (b i))) Finset.univ
    rw [@norm_sq_eq_re_inner ℂ, show (inner ℂ e e) = _ from h1]
    simp only [S, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.conj_conj, RCLike.re_to_complex, Complex.mul_conj, Complex.ofReal_re]
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have key := h e
  rw [hφe, hne, Complex.normSq_ofReal] at key
  rcases eq_or_lt_of_le hS with h0 | hpos
  · rw [← h0]; exact hM
  · nlinarith

end ONB

end GaloisForLFunctions.RHTower.SarnakXueInner
