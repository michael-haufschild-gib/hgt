import GaloisForLFunctions.HTGeometry.SchwartzOscillatorAlgebra
import GaloisForLFunctions.HTGeometry.HermiteL2Completeness
import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetKernel
import Mathlib.Analysis.PSeries

/-!
# Closed Fourier–jet source and its bounded-recovery boundary

The actual Hermite shift-by-four energy recurrence has no nonzero summable solution.
Consequently the Hermite tail alone excludes every weak collision of the Schwartz
operator C²+B². Continuous Schwartz test equations pass to the actual source graph closure;
both its input and output projections are injective.

The same tail theorem excludes a bounded left inverse of C²+B². Exact cancelling Schwartz
source pairs transfer this obstruction to bounded recovery of the first coordinate from
the maximal-domain physical Fourier–jet outputs.

The recovery obstruction holds on both the full and the even maximal-domain source.
Exact Hermite parity justifies the even restriction. Transfer to the finite arithmetic core
uses the graph-core theorem in `PrimeBurnolFourierJetPrimeCore`.
No Gamma–Xi identification, Hardy-index transfer, sub-unit bound, or RH assertion is made.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace SchwartzMap Real
open GaloisForLFunctions
noncomputable section
namespace RHTower

/-- The Hermite shift-by-four energy recurrence has no nonzero summable solution. -/
private theorem hermite_four_step_summable_zero (a : ℕ → ℝ) (ha : Summable a)
    (hnn : ∀ n, 0 ≤ a n)
    (hr : ∀ n : ℕ, ((n : ℝ)+3)*((n : ℝ)+4)*a (n+4) =
      ((n : ℝ)+1)*((n : ℝ)+2)*a n) : ∀ n, a n = 0 := by
  have hz (r : ℕ) : a (4+r) = 0 := by
    have hstep (k : ℕ) : (k : ℝ)*a (4*k+r) ≤ ((k : ℝ)+1)*a (4*(k+1)+r) := by
      have heq := hr (4*k+r)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at heq
      have hind : 4*k+r+4 = 4*(k+1)+r := by omega
      rw [hind] at heq
      have hd : 0 < (4*(k : ℝ)+(r : ℝ)+3)*(4*(k : ℝ)+(r : ℝ)+4) := by positivity
      have hid : ((4*(k : ℝ)+(r : ℝ)+3)*(4*(k : ℝ)+(r : ℝ)+4))*
          (((k : ℝ)+1)*a (4*(k+1)+r)-(k : ℝ)*a (4*k+r)) =
          (((4*(r : ℝ)+2)*(k : ℝ)+((r : ℝ)+1)*((r : ℝ)+2)))*a (4*k+r) := by
        linear_combination ((k : ℝ)+1)*heq
      have hp : 0 ≤ ((4*(k : ℝ)+(r : ℝ)+3)*(4*(k : ℝ)+(r : ℝ)+4))*
          (((k : ℝ)+1)*a (4*(k+1)+r)-(k : ℝ)*a (4*k+r)) := by
        rw [hid]
        exact mul_nonneg (by positivity) (hnn _)
      have hdiff : 0 ≤ ((k : ℝ)+1)*a (4*(k+1)+r)-(k : ℝ)*a (4*k+r) := by
        by_contra h
        exact (not_lt_of_ge hp) (mul_neg_of_pos_of_neg hd (lt_of_not_ge h))
      linarith
    have hb : ∀ k : ℕ, 1 ≤ k → a (4+r) ≤ (k : ℝ)*a (4*k+r) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => simp
      | succ k hk ih => simpa only [Nat.cast_add, Nat.cast_one] using ih.trans (hstep k)
    by_contra hne
    have hc : Summable (fun k : ℕ => a (4*k+r)) :=
      ha.comp_injective (by intro i j h; change 4*i+r = 4*j+r at h; omega)
    have hs : Summable (fun k : ℕ => a (4+r)/(k : ℝ)) := by
      apply Summable.of_nonneg_of_le (fun k => div_nonneg (hnn _) (Nat.cast_nonneg k)) _ hc
      intro k
      by_cases hk : k = 0
      · simp [hk, hnn]
      · have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
        apply (div_le_iff₀ hk0).mpr
        simpa only [mul_comm] using hb k (Nat.one_le_iff_ne_zero.mpr hk)
    have hinv : Summable (fun k : ℕ => (k : ℝ)⁻¹) := by
      apply (summable_mul_left_iff hne).mp
      simpa only [div_eq_mul_inv] using hs
    have hbad : (1 : ℕ) < 1 := Real.summable_nat_pow_inv.mp (by simpa using hinv)
    exact (Nat.lt_irrefl 1) hbad
  intro n
  have heq := hr n
  have h0 : a (n+4) = 0 := by simpa only [Nat.add_comm] using hz n
  rw [h0, mul_zero] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (by positivity)

private abbrev hL2 (n : ℕ) : SoninL2 := (hermiteSchwartz n).toLp 2 volume
private def hEnergy (u : SoninL2) (n : ℕ) : ℝ :=
  ‖⟪hL2 n, u⟫_ℂ‖^2 / ‖hL2 n‖^2

private theorem hNorm_pos (n : ℕ) : 0 < ‖hL2 n‖^2 :=
  pow_pos (norm_pos_iff.mpr (hermiteSchwartz_toLp_ne_zero n)) _

private theorem hNorm_succ (n : ℕ) :
    ‖hL2 (n+1)‖^2 = ((n : ℝ)+1)/π * ‖hL2 n‖^2 := by
  have h := schwartzPair_hermiteSchwartz_self_succ n
  rw [← inner_hermiteSchwartz_toLp, ← inner_hermiteSchwartz_toLp,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

private theorem hNorm_four (n : ℕ) :
    ‖hL2 (n+4)‖^2 =
      (((n : ℝ)+1)*((n : ℝ)+2)*((n : ℝ)+3)*((n : ℝ)+4)/π^4)*‖hL2 n‖^2 := by
  rw [show n+4=(n+3)+1 by omega, hNorm_succ,
    show n+3=(n+2)+1 by omega, hNorm_succ,
    show n+2=(n+1)+1 by omega, hNorm_succ, hNorm_succ]
  push_cast
  ring

private theorem hEnergy_summable (u : SoninL2) : Summable (hEnergy u) := by
  have h := orthonormal_hermiteSchwartz_toLp.inner_products_summable u
  apply h.congr
  intro n
  simp only [hEnergy, hL2, inner_smul_left, norm_mul, RCLike.norm_conj,
    norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_pow, inv_pow, div_eq_mul_inv, mul_comm]

/-- The actual squared creation/annihilation test map into physical L2. -/
def burnolJetWeakTest : 𝓢(ℝ, ℂ) →L[ℂ] SoninL2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp
    (creationCLM.comp creationCLM + annihilationCLM.comp annihilationCLM)

private theorem burnolJetWeakTest_hermite (n : ℕ) :
    burnolJetWeakTest (hermiteSchwartz (n+2)) =
      (4*(π : ℂ)^2) • hL2 (n+4) +
      (4*((n : ℂ)+1)*((n : ℂ)+2)) • hL2 n := by
  change (SchwartzMap.toLpCLM ℂ ℂ 2 volume)
    (creationCLM (creationCLM (hermiteSchwartz (n+2))) +
      annihilationCLM (annihilationCLM (hermiteSchwartz (n+2)))) = _
  rw [creationCLM_hermiteSchwartz, map_smul, creationCLM_hermiteSchwartz,
    show n+2=(n+1)+1 by omega, annihilationCLM_hermiteSchwartz, map_smul,
    annihilationCLM_hermiteSchwartz]
  simp only [map_add, map_smul, smul_smul, Nat.cast_add, Nat.cast_one,
    SchwartzMap.toLpCLM_apply]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

private theorem weak_hermite_coefficient (u : SoninL2)
    (hu : ∀ n : ℕ, ⟪burnolJetWeakTest (hermiteSchwartz (n+2)), u⟫_ℂ = 0) (n : ℕ) :
    ((π^2 : ℝ) : ℂ)*⟪hL2 (n+4), u⟫_ℂ =
      -((((n : ℝ)+1)*((n : ℝ)+2) : ℝ) : ℂ)*⟪hL2 n, u⟫_ℂ := by
  have h := hu n
  rw [burnolJetWeakTest_hermite, inner_add_left, inner_smul_left, inner_smul_left] at h
  simp only [map_mul, map_pow, map_add, map_ofNat, map_one, map_natCast, Complex.conj_ofReal] at h
  push_cast
  linear_combination (1/4 : ℂ)*h

private theorem weak_hEnergy_recurrence (u : SoninL2)
    (hu : ∀ n : ℕ, ⟪burnolJetWeakTest (hermiteSchwartz (n+2)), u⟫_ℂ = 0) (n : ℕ) :
    ((n : ℝ)+3)*((n : ℝ)+4)*hEnergy u (n+4) =
      ((n : ℝ)+1)*((n : ℝ)+2)*hEnergy u n := by
  have h := congrArg (fun z : ℂ => ‖z‖^2) (weak_hermite_coefficient u hu n)
  simp only [norm_mul, norm_neg] at h
  rw [Complex.norm_of_nonneg (sq_nonneg π),
    Complex.norm_of_nonneg (by positivity : 0 ≤ ((n : ℝ)+1)*((n : ℝ)+2))] at h
  simp only [mul_pow] at h
  unfold hEnergy
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_eq_div_iff (ne_of_gt (hNorm_pos (n+4))) (ne_of_gt (hNorm_pos n))).mpr
  rw [hNorm_four]
  field_simp
  linear_combination (‖hL2 n‖^2)*h

/-- The Hermite tail already excludes every weak collision, without a jet-domain premise. -/
theorem burnolJetWeakTest_hermite_tail_kernel (u : SoninL2)
    (hu : ∀ n : ℕ, ⟪burnolJetWeakTest (hermiteSchwartz (n+2)), u⟫_ℂ = 0) : u = 0 := by
  have hz := hermite_four_step_summable_zero (hEnergy u) (hEnergy_summable u)
    (fun n => div_nonneg (sq_nonneg _) (sq_nonneg _)) (weak_hEnergy_recurrence u hu)
  apply hermite_l2_complete
  intro n
  have h := hz n
  unfold hEnergy at h
  have hn : ‖⟪hL2 n, u⟫_ℂ‖^2 = 0 :=
    (div_eq_zero_iff.mp h).resolve_right (ne_of_gt (hNorm_pos n))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

private theorem burnolJetWeakTest_kernel (u : SoninL2)
    (hu : ∀ φ, ⟪burnolJetWeakTest φ, u⟫_ℂ = 0) : u = 0 :=
  burnolJetWeakTest_hermite_tail_kernel u (fun n => hu (hermiteSchwartz (n+2)))

private abbrev schLp : 𝓢(ℝ, ℂ) →L[ℂ] SoninL2 := SchwartzMap.toLpCLM ℂ ℂ 2 volume
private abbrev squareS (φ : 𝓢(ℝ, ℂ)) := mulXCLM (mulXCLM φ)
private abbrev deriv2S (φ : 𝓢(ℝ, ℂ)) := derivSCLM (derivSCLM φ)

private theorem square_schwartz_mem (φ : 𝓢(ℝ, ℂ)) :
    schLp φ ∈ burnolSquarePosition.domain := by
  change MemLp (fun x : ℝ => ((x^2 : ℝ) : ℂ)*(schLp φ) x) 2 volume
  apply (memLp_congr_ae _).mpr ((squareS φ).memLp 2 volume)
  filter_upwards [φ.coeFn_toLp 2 volume] with x hx
  change ((x^2 : ℝ) : ℂ)*φ.toLp 2 volume x = squareS φ x
  rw [hx]
  simp only [squareS, mulXCLM_apply, Complex.ofReal_pow]
  ring

private def squareSchwartz (φ : 𝓢(ℝ, ℂ)) : burnolSquarePosition.domain :=
  ⟨schLp φ, square_schwartz_mem φ⟩

private theorem square_schwartz_action (φ : 𝓢(ℝ, ℂ)) :
    burnolSquarePosition (squareSchwartz φ) = schLp (squareS φ) := by
  apply Lp.ext
  filter_upwards [HTGeometry.maximalRealL2Mul_apply_ae volume (fun x : ℝ => x^2)
      (squareSchwartz φ), φ.coeFn_toLp 2 volume, (squareS φ).coeFn_toLp 2 volume]
    with x hm hf hs
  change (burnolSquarePosition (squareSchwartz φ)) x =
    ((x^2 : ℝ) : ℂ)*φ.toLp 2 volume x at hm
  rw [hm]
  change ((x^2 : ℝ) : ℂ)*φ.toLp 2 volume x = (squareS φ).toLp 2 volume x
  rw [hs, hf]
  simp only [squareS, mulXCLM_apply, Complex.ofReal_pow]
  ring

private theorem square_schwartz_pair (φ : 𝓢(ℝ, ℂ)) (f : burnolSquarePosition.domain) :
    ⟪schLp φ, burnolSquarePosition f⟫_ℂ = ⟪schLp (squareS φ), (f : SoninL2)⟫_ℂ := by
  have h := HTGeometry.maximalRealL2Mul_formalSelfAdjoint volume (fun x : ℝ => x^2)
    (squareSchwartz φ) f
  change ⟪burnolSquarePosition (squareSchwartz φ), (f : SoninL2)⟫_ℂ =
    ⟪schLp φ, burnolSquarePosition f⟫_ℂ at h
  rw [square_schwartz_action] at h
  exact h.symm

private theorem fourier_schwartz (φ : 𝓢(ℝ, ℂ)) :
    fourierUnitary (schLp φ) = schLp (fourierSCLM φ) := SchwartzMap.toLp_fourier_eq φ

private theorem fourier_schwartz_second (φ : 𝓢(ℝ, ℂ)) :
    fourierUnitary (schLp (deriv2S φ)) =
      (-4*(π : ℂ)^2) • schLp (squareS (fourierSCLM φ)) := by
  rw [fourier_schwartz]
  change schLp (fourierSCLM (derivSCLM (derivSCLM φ))) = _
  rw [fourierSCLM_derivSCLM, fourierSCLM_derivSCLM]
  simp only [map_smul, smul_smul]
  congr 1
  calc
    _ = 4*(π : ℂ)^2*Complex.I^2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

private theorem burnolJetWeakTest_expansion (φ : 𝓢(ℝ, ℂ)) :
    burnolJetWeakTest φ = (8*(π : ℂ)^2) • schLp (squareS φ) +
      (2 : ℂ) • schLp (deriv2S φ) := by
  have h : creationCLM (creationCLM φ) + annihilationCLM (annihilationCLM φ) =
      (8*(π : ℂ)^2) • squareS φ + (2 : ℂ) • deriv2S φ := by
    simp only [creationCLM_eq, annihilationCLM_eq, map_sub, map_add, map_smul,
      squareS, deriv2S]
    module
  change schLp (creationCLM (creationCLM φ) + annihilationCLM (annihilationCLM φ)) = _
  rw [h, map_add, map_smul, map_smul]

private def jetGraphEmbedding : (burnolSquarePosition.domain × burnolSquarePosition.domain) →ₗ[ℂ]
    ((SoninL2 × SoninL2) × (SoninL2 × SoninL2)) where
  toFun z := (((z.1 : SoninL2), (z.2 : SoninL2)), primeBurnolFourierJetSynthesis z)
  map_add' z w := Prod.ext rfl (map_add primeBurnolFourierJetSynthesis z w)
  map_smul' c z := Prod.ext rfl (map_smul primeBurnolFourierJetSynthesis c z)

/-- The actual graph closure of the maximal-domain literal Fourier–jet source. -/
def primeBurnolFourierJetClosedGraph :
    Submodule ℂ ((SoninL2 × SoninL2) × (SoninL2 × SoninL2)) :=
  jetGraphEmbedding.range.topologicalClosure

private theorem closed_graph_first {w : (SoninL2 × SoninL2) × (SoninL2 × SoninL2)}
    (hw : w ∈ primeBurnolFourierJetClosedGraph) :
    w.1.1 + fourierUnitary w.1.2 = w.2.1 := by
  have hsub : (jetGraphEmbedding.range : Set ((SoninL2 × SoninL2) × (SoninL2 × SoninL2))) ⊆
      {v | v.1.1 + fourierUnitary v.1.2 = v.2.1} := by
    rintro v ⟨z, rfl⟩
    rfl
  exact closure_minimal hsub (isClosed_eq (by fun_prop) (by fun_prop)) hw

private theorem closed_graph_test {w : (SoninL2 × SoninL2) × (SoninL2 × SoninL2)}
    (hw : w ∈ primeBurnolFourierJetClosedGraph) (φ : 𝓢(ℝ, ℂ)) :
    ⟪schLp (fourierSCLM φ), w.2.2⟫_ℂ =
      ⟪schLp (squareS (fourierSCLM φ)), w.1.1⟫_ℂ +
      ⟪schLp (squareS φ), w.1.2⟫_ℂ := by
  have hsub : (jetGraphEmbedding.range : Set ((SoninL2 × SoninL2) × (SoninL2 × SoninL2))) ⊆
      {v | ⟪schLp (fourierSCLM φ), v.2.2⟫_ℂ =
        ⟪schLp (squareS (fourierSCLM φ)), v.1.1⟫_ℂ +
        ⟪schLp (squareS φ), v.1.2⟫_ℂ} := by
    rintro v ⟨⟨f, g⟩, rfl⟩
    change ⟪schLp (fourierSCLM φ),
        burnolSquarePosition f + fourierUnitary (burnolSquarePosition g)⟫_ℂ = _
    rw [inner_add_right, square_schwartz_pair]
    congr 1
    rw [← fourier_schwartz, fourierUnitary.inner_map_map, square_schwartz_pair]
    rfl
  exact closure_minimal hsub (isClosed_eq (by fun_prop) (by fun_prop)) hw

private theorem closed_graph_zero_output {z : SoninL2 × SoninL2}
    (hz : (z, 0) ∈ primeBurnolFourierJetClosedGraph) : z = 0 := by
  have hf : z.1 = -fourierUnitary z.2 := eq_neg_of_add_eq_zero_left (closed_graph_first hz)
  have hg : z.2 = 0 := by
    apply burnolJetWeakTest_kernel
    intro φ
    have ht := closed_graph_test hz φ
    change ⟪schLp (fourierSCLM φ), (0 : SoninL2)⟫_ℂ = _ at ht
    rw [inner_zero_right, hf, inner_neg_right] at ht
    have hd := congrArg (fun v : SoninL2 => ⟪v, fourierUnitary z.2⟫_ℂ)
      (fourier_schwartz_second φ)
    simp only [fourierUnitary.inner_map_map, inner_smul_left,
      map_neg, map_mul, map_ofNat, map_pow, Complex.conj_ofReal] at hd
    rw [burnolJetWeakTest_expansion, inner_add_left, inner_smul_left, inner_smul_left]
    simp only [map_mul, map_pow, map_ofNat, Complex.conj_ofReal]
    linear_combination -(8*(π : ℂ)^2)*ht + 2*hd
  have hf0 : z.1 = 0 := by simpa only [hg, map_zero, neg_zero] using hf
  exact Prod.ext hf0 hg

private theorem closed_graph_zero_input {y : SoninL2 × SoninL2}
    (hy : (0, y) ∈ primeBurnolFourierJetClosedGraph) : y = 0 := by
  have hy1 : y.1 = 0 := by
    have h := closed_graph_first hy
    change (0 : SoninL2) + fourierUnitary (0 : SoninL2) = y.1 at h
    simpa only [map_zero, add_zero] using h.symm
  have hy2' : fourierUnitary.symm y.2 = 0 := by
    apply hermite_l2_complete
    intro n
    have ht := closed_graph_test hy (hermiteSchwartz n)
    change ⟪schLp (fourierSCLM (hermiteSchwartz n)), y.2⟫_ℂ =
      ⟪_, (0 : SoninL2)⟫_ℂ + ⟪_, (0 : SoninL2)⟫_ℂ at ht
    simp only [inner_zero_right, add_zero] at ht
    rw [← fourierUnitary.inner_map_map (hL2 n) (fourierUnitary.symm y.2),
      fourierUnitary.apply_symm_apply]
    change ⟪fourierUnitary (schLp (hermiteSchwartz n)), y.2⟫_ℂ = 0
    rw [fourier_schwartz]
    exact ht
  have hy2 : y.2 = 0 := by
    rw [← fourierUnitary.apply_symm_apply y.2, hy2', map_zero]
  exact Prod.ext hy1 hy2

def primeBurnolFourierJetClosedInput :
    primeBurnolFourierJetClosedGraph →ₗ[ℂ] (SoninL2 × SoninL2) where
  toFun w := w.val.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def primeBurnolFourierJetClosedOutput :
    primeBurnolFourierJetClosedGraph →ₗ[ℂ] (SoninL2 × SoninL2) where
  toFun w := w.val.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Closing the actual graph does not create a nonzero output at zero input. -/
theorem primeBurnolFourierJetClosedInput_injective :
    Function.Injective primeBurnolFourierJetClosedInput := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have hin : w.val.1 = 0 := hw
  have hm := w.property
  have hpair : w.val = (0, w.val.2) := Prod.ext hin rfl
  rw [hpair] at hm
  exact Subtype.ext (Prod.ext hin (closed_graph_zero_input hm))

/-- The closed literal Fourier–jet source retains every physical input without collision. -/
theorem primeBurnolFourierJetClosedOutput_injective :
    Function.Injective primeBurnolFourierJetClosedOutput := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have hout : w.val.2 = 0 := hw
  have hm := w.property
  have hpair : w.val = (w.val.1, 0) := Prod.ext rfl hout
  rw [hpair] at hm
  exact Subtype.ext (Prod.ext (closed_graph_zero_output hm) hout)
/-- The weak test map has no bounded physical L2 left inverse. -/
theorem burnolJetWeakTest_no_bounded_leftInverse :
    ¬ ∃ T : SoninL2 →L[ℂ] SoninL2, ∀ φ, T (burnolJetWeakTest φ) = schLp φ := by
  rintro ⟨T, hT⟩
  have hu : T.adjoint (hL2 0) = 0 := by
    apply burnolJetWeakTest_hermite_tail_kernel
    intro n
    rw [ContinuousLinearMap.adjoint_inner_right, hT]
    apply inner_hermiteSchwartz_toLp_eq_zero
    omega
  have h := T.adjoint_inner_right (burnolJetWeakTest (hermiteSchwartz 0)) (hL2 0)
  rw [hu, inner_zero_right, hT] at h
  exact hermiteSchwartz_toLp_ne_zero 0 (inner_self_eq_zero.mp h.symm)

private def cancellingJetPair (φ : 𝓢(ℝ, ℂ)) :
    burnolSquarePosition.domain × burnolSquarePosition.domain :=
  (squareSchwartz (fourierSCLM φ), -squareSchwartz φ)

private theorem cancellingJetPair_output (φ : 𝓢(ℝ, ℂ)) :
    primeBurnolFourierJetSynthesis (cancellingJetPair φ) =
      (0, -((8*(π : ℂ)^2)⁻¹) • fourierUnitary (burnolJetWeakTest φ)) := by
  have hW : fourierUnitary (burnolJetWeakTest φ) =
      (8*(π : ℂ)^2) • fourierUnitary (schLp (squareS φ)) -
        (8*(π : ℂ)^2) • schLp (squareS (fourierSCLM φ)) := by
    rw [burnolJetWeakTest_expansion, map_add, map_smul, map_smul,
      fourier_schwartz_second, smul_smul]
    module
  have hc : -((8*(π : ℂ)^2)⁻¹)*(8*(π : ℂ)^2) = -1 := by
    have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  apply Prod.ext
  · change schLp (fourierSCLM φ) + fourierUnitary (-(schLp φ)) = 0
    rw [← fourier_schwartz, map_neg, add_neg_cancel]
  · change burnolSquarePosition.toFun (squareSchwartz (fourierSCLM φ)) +
        fourierUnitary (burnolSquarePosition.toFun (-squareSchwartz φ)) = _
    rw [map_neg, map_neg]
    rw [← sub_eq_add_neg]
    change burnolSquarePosition (squareSchwartz (fourierSCLM φ)) -
      fourierUnitary (burnolSquarePosition (squareSchwartz φ)) = _
    rw [square_schwartz_action, square_schwartz_action, hW, smul_sub, smul_smul, smul_smul, hc]
    module

/-- Even the first source coordinate has no bounded recovery from the physical jet outputs. -/
theorem primeBurnolFourierJet_no_bounded_first_recovery :
    ¬ ∃ R : (SoninL2 × SoninL2) →L[ℂ] SoninL2,
      ∀ z : burnolSquarePosition.domain × burnolSquarePosition.domain,
        R (primeBurnolFourierJetSynthesis z) = (z.1 : SoninL2) := by
  rintro ⟨R, hR⟩
  let channel : SoninL2 →L[ℂ] (SoninL2 × SoninL2) :=
    (0 : SoninL2 →L[ℂ] SoninL2).prod
      (-((8*(π : ℂ)^2)⁻¹) • fourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap)
  let T : SoninL2 →L[ℂ] SoninL2 :=
    fourierUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (R.comp channel)
  apply burnolJetWeakTest_no_bounded_leftInverse
  refine ⟨T, ?_⟩
  intro φ
  change fourierUnitary.symm
    (R (0, -((8*(π : ℂ)^2)⁻¹) • fourierUnitary (burnolJetWeakTest φ))) = schLp φ
  rw [← cancellingJetPair_output, hR]
  change fourierUnitary.symm (schLp (fourierSCLM φ)) = schLp φ
  rw [← fourier_schwartz, fourierUnitary.symm_apply_apply]

private theorem hL2_reflection (n : ℕ) :
    l2Reflection (hL2 n) = (-1 : ℂ)^n • hL2 n := by
  have hn := ((hermiteSchwartz n).coeFn_toLp 2 volume).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards [l2Reflection_ae (hL2 n), hn,
    Lp.coeFn_smul ((-1 : ℂ)^n) (hL2 n), (hermiteSchwartz n).coeFn_toLp 2 volume]
    with x hr hn hs hh
  change (hL2 n) (-x) = hermiteSchwartz n (-x) at hn
  change (hL2 n) x = hermiteSchwartz n x at hh
  rw [hr, hn, hs, Pi.smul_apply, hh, hermiteSchwartz_neg, smul_eq_mul]

private theorem hL2_even (k : ℕ) : hL2 (2*k) ∈ evenSubspace := by
  rw [mem_evenSubspace_iff, hL2_reflection]
  norm_num [pow_mul]

private theorem evenProjection_hL2_even (k : ℕ) : evenProjection (hL2 (2*k)) = hL2 (2*k) := by
  rw [evenProjection_apply, hL2_reflection]
  norm_num [pow_mul]
  module

private theorem evenProjection_hL2_odd (k : ℕ) : evenProjection (hL2 (2*k+1)) = 0 := by
  rw [evenProjection_apply, hL2_reflection]
  norm_num [pow_add, pow_mul]

private theorem evenProjection_weak_even (k : ℕ) :
    evenProjection (burnolJetWeakTest (hermiteSchwartz (2*k+2))) =
      burnolJetWeakTest (hermiteSchwartz (2*k+2)) := by
  rw [burnolJetWeakTest_hermite, map_add, map_smul, map_smul,
    show 2*k+4=2*(k+2) by omega, evenProjection_hL2_even, evenProjection_hL2_even]

private theorem evenProjection_weak_odd (k : ℕ) :
    evenProjection (burnolJetWeakTest (hermiteSchwartz ((2*k+1)+2))) = 0 := by
  rw [burnolJetWeakTest_hermite, map_add, map_smul, map_smul,
    show (2*k+1)+4=2*(k+2)+1 by omega, evenProjection_hL2_odd, evenProjection_hL2_odd]
  simp

private theorem weak_hermite_zero :
    burnolJetWeakTest (hermiteSchwartz 0) = (4*(π : ℂ)^2) • hL2 2 := by
  change schLp (creationCLM (creationCLM (hermiteSchwartz 0)) +
    annihilationCLM (annihilationCLM (hermiteSchwartz 0))) = _
  rw [creationCLM_hermiteSchwartz, map_smul, creationCLM_hermiteSchwartz,
    annihilationCLM_hermiteSchwartz_zero, map_zero, add_zero, map_smul, map_smul, smul_smul]
  congr 1
  ring

/-- Bounded first-coordinate recovery also fails on the even maximal-domain source itself. -/
theorem primeBurnolFourierJet_no_bounded_even_recovery :
    ¬ ∃ R : (SoninL2 × SoninL2) →L[ℂ] SoninL2,
      ∀ f g : burnolSquarePosition.domain,
        (f : SoninL2) ∈ evenSubspace → (g : SoninL2) ∈ evenSubspace →
        R (primeBurnolFourierJetSynthesis (f,g)) = (f : SoninL2) := by
  rintro ⟨R,hR⟩
  let channel : SoninL2 →L[ℂ] (SoninL2 × SoninL2) :=
    (0 : SoninL2 →L[ℂ] SoninL2).prod
      (-((8*(π : ℂ)^2)⁻¹) • fourierUnitary.toContinuousLinearEquiv.toContinuousLinearMap)
  let T : SoninL2 →L[ℂ] SoninL2 :=
    fourierUnitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (R.comp (channel.comp evenProjection))
  have htest (φ : 𝓢(ℝ, ℂ)) (he : schLp φ ∈ evenSubspace)
      (hW : evenProjection (burnolJetWeakTest φ) = burnolJetWeakTest φ) :
      T (burnolJetWeakTest φ) = schLp φ := by
    have hf : schLp (fourierSCLM φ) ∈ evenSubspace := by
      rw [← fourier_schwartz, mem_evenSubspace_iff, ← fourierUnitary_l2Reflection,
        (mem_evenSubspace_iff _).mp he]
    have hn : (-squareSchwartz φ : burnolSquarePosition.domain).val ∈ evenSubspace :=
      evenSubspace.neg_mem he
    change fourierUnitary.symm
      (R (0, -((8*(π : ℂ)^2)⁻¹) • fourierUnitary
        (evenProjection (burnolJetWeakTest φ)))) = schLp φ
    rw [hW, ← cancellingJetPair_output]
    change fourierUnitary.symm (R (primeBurnolFourierJetSynthesis
      (squareSchwartz (fourierSCLM φ), -squareSchwartz φ))) = schLp φ
    rw [hR _ _ hf hn]
    change fourierUnitary.symm (schLp (fourierSCLM φ)) = schLp φ
    rw [← fourier_schwartz, fourierUnitary.symm_apply_apply]
  have htail (n : ℕ) : ⟪T (burnolJetWeakTest (hermiteSchwartz (n+2))), hL2 0⟫_ℂ = 0 := by
    obtain ⟨k, h | h⟩ := Nat.even_or_odd' n
    · subst n
      have he : schLp (hermiteSchwartz (2*k+2)) ∈ evenSubspace := by
        change hL2 (2*k+2) ∈ evenSubspace
        rw [show 2*k+2=2*(k+1) by omega]
        exact hL2_even (k+1)
      rw [htest _ he (evenProjection_weak_even k)]
      apply inner_hermiteSchwartz_toLp_eq_zero
      omega
    · subst n
      have hz : T (burnolJetWeakTest (hermiteSchwartz ((2*k+1)+2))) = 0 := by
        change fourierUnitary.symm (R (channel
          (evenProjection (burnolJetWeakTest (hermiteSchwartz ((2*k+1)+2)))))) = 0
        rw [evenProjection_weak_odd, map_zero, map_zero, map_zero]
      rw [hz, inner_zero_left]
  have hu : T.adjoint (hL2 0) = 0 := by
    apply burnolJetWeakTest_hermite_tail_kernel
    intro n
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact htail n
  have he0 : schLp (hermiteSchwartz 0) ∈ evenSubspace := hL2_even 0
  have hW0 : evenProjection (burnolJetWeakTest (hermiteSchwartz 0)) =
      burnolJetWeakTest (hermiteSchwartz 0) := by
    rw [weak_hermite_zero, map_smul]
    exact congrArg ((4*(π : ℂ)^2) • ·) (evenProjection_hL2_even 1)
  have h := T.adjoint_inner_right (burnolJetWeakTest (hermiteSchwartz 0)) (hL2 0)
  rw [hu, inner_zero_right, htest _ he0 hW0] at h
  exact hermiteSchwartz_toLp_ne_zero 0 (inner_self_eq_zero.mp h.symm)

/-- The exact admitted cancelling source retains the position-square image of its second input. -/
theorem burnolJetSchwartz_cancelling_source (φ : 𝓢(ℝ, ℂ)) :
    ∃ f g : burnolSquarePosition.domain,
      (f : SoninL2) = fourierUnitary (φ.toLp 2 volume) ∧
      (g : SoninL2) = -(φ.toLp 2 volume) ∧
      burnolSquarePosition g = -((mulXCLM (mulXCLM φ)).toLp 2 volume) ∧
      primeBurnolFourierJetSynthesis (f,g) =
        (0, -((8*(π : ℂ)^2)⁻¹) • fourierUnitary (burnolJetWeakTest φ)) := by
  refine ⟨(cancellingJetPair φ).1, (cancellingJetPair φ).2,
    (fourier_schwartz φ).symm, rfl, ?_, cancellingJetPair_output φ⟩
  change burnolSquarePosition.toFun (-squareSchwartz φ) = _
  rw [map_neg]
  exact congrArg Neg.neg (square_schwartz_action φ)

end RHTower
