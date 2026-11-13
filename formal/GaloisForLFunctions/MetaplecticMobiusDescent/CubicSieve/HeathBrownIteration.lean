/-
The Heath-Brown iteration adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.PairedCubicReflection

/-!
# The Heath-Brown iteration

Dyadic decay constants and the Poisson envelope of descendants (`CubicDyadicDecay`); the
exponent improvement `HasCubicExponent.improve` of the Heath-Brown iteration down to the sharp
sieve bound; squarefree Gauss coefficients.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicDyadicDecay
open scoped BigOperators
noncomputable section

def decayConstant (α : ℝ) : ℝ :=
  (2 : ℝ)^α / ((2 : ℝ)^α - 1) + (1 - (2 : ℝ)^(α - 3))⁻¹

lemma dyadic_rpow (α : ℝ) (j : ℕ) :
    ((2 : ℝ)^j)^α = ((2 : ℝ)^α)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]

lemma decay_le_low (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤ ((2 : ℝ)^α)^j := by
  rw [← dyadic_rpow]
  exact div_le_self (by positivity) (one_le_pow₀ (by
    have : 0 ≤ t * (2 : ℝ)^j := by positivity
    linarith))

lemma decay_le_high (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j := by
  have hk : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ((2 : ℝ)^j)^α / (t * (2 : ℝ)^j)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 3)
    _ = _ := by
      rw [← dyadic_rpow, Real.rpow_sub hk, Real.rpow_neg ht.le, mul_pow]
      simp only [Real.rpow_ofNat]
      ring

lemma decay_summable (t α : ℝ) (ht : 0 < t) (hα : α < 3) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) := by
  have hr : (2 : ℝ)^(α - 3) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ((summable_geometric_of_lt_one (by positivity) hr).mul_left (t^(-3 : ℝ))).of_nonneg_of_le
    (fun j => by positivity) (decay_le_high t α ht)

lemma decayConstant_pos (α : ℝ) (hα : 0 < α) (hα3 : α < 3) :
    0 < decayConstant α := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold decayConstant
  positivity

lemma geometric_prefix_le (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (∑ j ∈ Finset.range k, q^j) ≤ q^k / (q - 1) := by
  rw [geom_sum_eq (ne_of_gt hq)]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma decay_tail_le (t α : ℝ) (ht : 0 < t) (hα3 : α < 3) (k : ℕ) :
    (∑' j : ℕ, ((2 : ℝ)^(j+k))^α / (1 + t * (2 : ℝ)^(j+k))^3) ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k * (1 - (2 : ℝ)^(α-3))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(α-3) := by positivity
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs := summable_geometric_of_lt_one hr0 hr
  calc
    _ ≤ ∑' j : ℕ, t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^(j+k) := by
      apply (decay_summable t α ht hα3).comp_injective (add_left_injective k) |>.tsum_le_tsum
        (fun j => decay_le_high t α ht (j+k))
      exact (hs.comp_injective (add_left_injective k)).mul_left _
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr]
      ring

theorem dyadic_decay_bound (t α : ℝ) (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑' j : ℕ, ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
      decayConstant α * t^(-α) := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < (1 - (2 : ℝ)^(α-3))⁻¹ := inv_pos.mpr (by linarith)
  by_cases ht1 : 1 ≤ t
  · have hp : t^(-3 : ℝ) ≤ t^(-α) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hh := decay_tail_le t α ht hα3 0
    simp only [Nat.add_zero, pow_zero, mul_one] at hh
    apply hh.trans
    unfold decayConstant
    nlinarith [mul_nonneg (div_nonneg (by positivity : 0 ≤ (2 : ℝ)^α)
      (by linarith : 0 ≤ (2 : ℝ)^α - 1)) (by positivity : 0 ≤ t^(-α)),
      mul_le_mul_of_nonneg_right hp hden.le]
  · have hit : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr (le_of_not_ge ht1)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hit (by norm_num : (1 : ℝ) < 2)
    let k := n+1
    have hk0 : 0 < (2 : ℝ)^k := by positivity
    have hk : t⁻¹ ≤ (2 : ℝ)^k := le_of_lt hn'
    have hk' : (2 : ℝ)^k ≤ 2*t⁻¹ := by
      dsimp [k]
      rw [pow_succ]
      nlinarith
    have hlow : (∑ j ∈ Finset.range k,
        ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
        (2 : ℝ)^α / ((2 : ℝ)^α - 1) * t^(-α) := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, ((2 : ℝ)^α)^j :=
          Finset.sum_le_sum (fun j hj => decay_le_low t α ht j)
        _ ≤ ((2 : ℝ)^α)^k / ((2 : ℝ)^α - 1) := geometric_prefix_le _ hq k
        _ ≤ (2*t⁻¹)^α / ((2 : ℝ)^α - 1) := by
          rw [← dyadic_rpow]
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hk0.le hk' hα.le)
            (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ht.le),
            ← Real.rpow_neg_eq_inv_rpow]
          ring
    have hhigh : t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k ≤ t^(-α) := by
      rw [← dyadic_rpow]
      calc
        _ ≤ t^(-3 : ℝ) * (t⁻¹)^(α-3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ht)
            hk (by linarith)) (by positivity)
        _ = _ := by
          rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add ht]
          congr 1
          ring
    rw [← (decay_summable t α ht hα3).sum_add_tsum_nat_add k]
    have htail := (decay_tail_le t α ht hα3 k).trans
      (mul_le_mul_of_nonneg_right hhigh hden.le)
    unfold decayConstant
    nlinarith

theorem two_power_majorant (B : ℝ → ℝ) (C P Q t α β : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t)
    (hα : 0 < α) (hα3 : α < 3) (hβ : 0 < β) (hβ3 : β < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ C * (P*K^α + Q*K^β)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ≤
      C * (P*decayConstant α*t^(-α) + Q*decayConstant β*t^(-β)) := by
  let f (γ : ℝ) (j : ℕ) := ((2 : ℝ)^j)^γ / (1+t*(2 : ℝ)^j)^3
  have hsα : Summable (f α) := decay_summable t α ht hα3
  have hsβ : Summable (f β) := decay_summable t β ht hβ3
  have hs : Summable (fun j => C*(P*f α j+Q*f β j)) :=
    ((hsα.mul_left P).add (hsβ.mul_left Q)).mul_left C
  have hle (j : ℕ) : B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3 ≤
      C*(P*f α j+Q*f β j) := by
    have hi := div_le_div_of_nonneg_right (hB ((2 : ℝ)^j)
      (one_le_pow₀ (by norm_num))) (by positivity : 0 ≤ (1+t*(2 : ℝ)^j)^3)
    dsimp [f]
    convert hi using 1 <;> first | rfl | ring
  have hsum := hs.of_nonneg_of_le
    (fun j => div_nonneg (hB0 _ (one_le_pow₀ (by norm_num))) (by positivity)) hle
  refine ⟨hsum, (hsum.tsum_le_tsum hle hs).trans ?_⟩
  rw [tsum_mul_left, (hsα.mul_left P).tsum_add (hsβ.mul_left Q), tsum_mul_left,
    tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hC
  have h₁ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t α ht hα hα3) hP
  have h₂ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t β ht hβ hβ3) hQ
  dsimp [f] at *
  nlinarith

theorem sieve_growth_majorant (B : ℝ → ℝ) (A N t δ ξ : ℝ)
    (hA : 0 ≤ A) (hN : 0 < N) (ht : 0 < t)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ≤
      A*N^δ * (N*decayConstant (1/3+δ)*t^(-(1/3+δ)) +
        decayConstant (ξ+δ)*t^(-(ξ+δ))) := by
  have hh := two_power_majorant B (A*N^δ) N 1 t (1/3+δ) (ξ+δ)
    (by positivity) hN.le (by norm_num) ht hα hα3 hβ hβ3 hB0
  simp only [one_mul] at hh
  apply hh
  intro K hK
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  apply (hB K hK).trans_eq
  rw [Real.mul_rpow hK0.le hN.le, Real.rpow_add hK0, Real.rpow_add hK0]
  ring

lemma poisson_scale_identity (M N α : ℝ) (hM : 0 < M) (hN : 0 < N) :
    M/N * (M/N^2)^(-α) = M^(1-α) * N^(2*α-1) := by
  rw [Real.div_rpow hM.le (sq_nonneg N), Real.rpow_neg hM.le,
    Real.rpow_neg (sq_nonneg N), div_inv_eq_mul,
    ← Real.rpow_natCast_mul hN.le 2 α, Real.rpow_sub hM,
    Real.rpow_sub hN, Real.rpow_one, Real.rpow_one]
  norm_num
  ring

lemma poisson_small_power_identity (M N δ β : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^δ * (M/N) * (M/N^2)^(-(β+δ)) =
      N^(3*δ)*M^(-δ)*M^(1-β)*N^(2*β-1) := by
  rw [mul_assoc, poisson_scale_identity M N (β+δ) hM hN]
  calc
    _ = M^(1-(β+δ)) * (N^δ*N^(2*(β+δ)-1)) := by ring
    _ = M^(-δ+(1-β)) * N^(3*δ+(2*β-1)) := by
      rw [← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> first | rfl | ring
    _ = _ := by rw [Real.rpow_add hM, Real.rpow_add hN]; ring

theorem sieve_poisson_bound (B : ℝ → ℝ) (A M N δ ξ : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    (M/N) * (∑' j : ℕ, B ((2 : ℝ)^j) / (1+M*(2 : ℝ)^j/N^2)^3) ≤
      A*N^(3*δ)*M^(-δ) *
        (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
          decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1)) := by
  have ht : 0 < M/N^2 := by positivity
  have hh := (sieve_growth_majorant B A N (M/N^2) δ ξ hA hN ht
    hα hα3 hβ hβ3 hB0 hB).2
  have hden : (fun j : ℕ => B ((2 : ℝ)^j)/(1+(M/N^2)*(2 : ℝ)^j)^3) =
      (fun j : ℕ => B ((2 : ℝ)^j)/(1+M*(2 : ℝ)^j/N^2)^3) := by
    funext j
    congr 2
    ring
  rw [hden] at hh
  apply (mul_le_mul_of_nonneg_left hh (div_pos hM hN).le).trans_eq
  have hid₁ := poisson_small_power_identity M N δ (1/3) hM hN
  have hid₂ := poisson_small_power_identity M N δ ξ hM hN
  have hmix : N * M^(1-(1/3 : ℝ)) * N^(2*(1/3 : ℝ)-1) =
      (M*N)^(2/3 : ℝ) := by
    norm_num
    rw [Real.mul_rpow hM.le hN.le]
    have hn' : N * N^(- (1/3 : ℝ)) = N^(2/3 : ℝ) := by
      calc
        _ = N^(1 : ℝ) * N^(-(1/3 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN]; norm_num
    nlinarith [congrArg (fun x => M^(2/3 : ℝ)*x) hn']
  calc
    _ = A*N*decayConstant (1/3+δ)*(N^δ*(M/N)*(M/N^2)^(-(1/3+δ))) +
        A*decayConstant (ξ+δ)*(N^δ*(M/N)*(M/N^2)^(-(ξ+δ))) := by ring
    _ = _ := by
      rw [hid₁, hid₂]
      have he := congrArg (fun x => A*N^(3*δ)*M^(-δ)*decayConstant (1/3+δ)*x) hmix
      nlinarith [he]

lemma descent_factor_le_one (e d u v : ℝ) (he : 1 ≤ e) (hed : e ≤ d)
    (hv : v ≤ 0) (huv : u+v ≤ 0) : e^u*d^v ≤ 1 := by
  have hd : 1 ≤ d := he.trans hed
  by_cases hu : 0 ≤ u
  · calc
      _ ≤ d^u*d^v := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by linarith) hed hu) (by positivity)
      _ = d^(u+v) := (Real.rpow_add (by linarith : 0 < d) u v).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd huv
  · exact (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos he (le_of_not_ge hu))
      (Real.rpow_le_one_of_one_le_of_nonpos hd hv) (by positivity) (by norm_num)).trans_eq
      (one_mul 1)

lemma monomial_descendant_le (M N e d u v : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hv : 0 ≤ v) (huv : 0 ≤ u+v) :
    (M/e)^u*(N/d)^v ≤ M^u*N^v := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  have hg := descent_factor_le_one e d (-u) (-v) he hed (by linarith) (by linarith)
  calc
    _ = (M^u*N^v)*(e^(-u)*d^(-v)) := by
      rw [Real.div_rpow hM.le he0.le, Real.div_rpow hN.le hd0.le,
        Real.rpow_neg he0.le, Real.rpow_neg hd0.le]
      ring
    _ ≤ (M^u*N^v)*1 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := mul_one _

lemma mixed_monomial_identity (M N δ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) =
      M^(2/3-δ)*N^(2/3+3*δ) := by
  rw [Real.mul_rpow hM.le hN.le]
  calc
    _ = (M^(-δ)*M^(2/3 : ℝ))*(N^(3*δ)*N^(2/3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> first | rfl | ring

lemma secondary_monomial_identity (M N δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) =
      M^(1-ξ-δ)*N^(2*ξ-1+3*δ) := by
  calc
    _ = (M^(-δ)*M^(1-ξ))*(N^(3*δ)*N^(2*ξ-1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> first | rfl | ring

lemma mixed_descendant_le (M N e d δ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*((M/e)*(N/d))^(2/3 : ℝ) ≤
      N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [mixed_monomial_identity (M/e) (N/d) δ (div_pos hM he0) (div_pos hN hd0),
    mixed_monomial_identity M N δ hM hN]
  exact monomial_descendant_le M N e d (2/3-δ) (2/3+3*δ) hM hN he hed
    (by linarith) (by linarith)

lemma secondary_descendant_le (M N e d δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1) ≤
      N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [secondary_monomial_identity (M/e) (N/d) δ ξ (div_pos hM he0) (div_pos hN hd0),
    secondary_monomial_identity M N δ ξ hM hN]
  exact monomial_descendant_le M N e d (1-ξ-δ) (2*ξ-1+3*δ) hM hN he hed
    (by linarith) (by linarith)

theorem poisson_envelope_descendant_le (M N e d δ ξ P Q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (N/d)^(3*δ)*(M/e)^(-δ) *
        (P*((M/e)*(N/d))^(2/3 : ℝ) + Q*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)) ≤
      N^(3*δ)*M^(-δ) * (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1)) := by
  have hm := mul_le_mul_of_nonneg_left (mixed_descendant_le M N e d δ hM hN he hed hδ) hP
  have hs := mul_le_mul_of_nonneg_left
    (secondary_descendant_le M N e d δ ξ hM hN he hed hδ hξ) hQ
  nlinarith [hm, hs]

end
end CubicDyadicDecay

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
noncomputable section
local notation "O" => Eisenstein.O

theorem elementSieveNorm_two_power_log (ξ ε A M N : ℝ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hB1 : ∀ X : ℝ, 1 ≤ X → sieveNorm (2*X) N ≤
      A*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ))) :
    elementSieveNorm M N ≤ (384*128^2 : ℝ) * A *
      (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
      (M*N)^ε * (M^(1/3 : ℝ)*N + M^ξ) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let R := elementRange M
  have hRne : R.Nonempty := by
    refine ⟨1, ?_⟩
    rw [mem_elementRange]
    refine ⟨one_ne_zero, ?_⟩
    simpa using hM
  have hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    fun z hz => (mem_elementRange M z).mp hz
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  obtain ⟨X,Y,hX,hY,hXY,he⟩ := full_element_dyadic_extraction R hRne M N hR
    (fun j : idealRange N => j.val) Subtype.val_injective
    (fun j => mem_idealRange.mp j.property) a
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hXM : X ≤ M := by nlinarith [sq_nonneg (Y-1)]
  have hYM : Y ≤ M := by nlinarith [sq_nonneg (Y-1)]
  let B := A*(M*N)^ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (U : ℝ) (hU : 1 ≤ U) (hUM : U ≤ M) :
      sieveNorm (2*U) N ≤ B*(U^ξ+N+(U*N)^(2/3 : ℝ)) := by
    apply (hB1 U hU).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right hUM hN0.le) hε) hA
  have hmin : min (Y*sieveNorm (2*X) N) (X*sieveNorm (2*Y) N) ≤
      B*min (Y*(X^ξ+N+(X*N)^(2/3 : ℝ))) (X*(Y^ξ+N+(Y*N)^(2/3 : ℝ))) := by
    rw [mul_min_of_nonneg _ _ hB]
    apply min_le_min
    · convert mul_le_mul_of_nonneg_left (hb X hX hXM) hY0.le using 1; ring
    · convert mul_le_mul_of_nonneg_left (hb Y hY hYM) hX0.le using 1; ring
  have hopt := extraction_min_two_power M N X Y ξ hM hN0.le hX hY hXY hξ
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hi (z : O) : (∑ j : idealRange N, a j * elementCharacter j.val (mem_idealRange.mp j.property).1.2 z) =
      ∑ j : idealRange N, cubicRow j.val z * a j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  simp_rw [hi] at he
  have hE : 0 ≤ ∑ j : idealRange N, ‖a j‖^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (show 0 ≤ (192*128^2 : ℝ)*
      (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M/(X*Y^2))^(1/3 : ℝ) by positivity)) hE
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hopt (show 0 ≤ (192*128^2 : ℝ)*
      (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*B by positivity)) hE
  have he' := he.trans hh
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val * a j‖^2) ≤ _
  apply he'.trans
  convert hbnd using 1 <;> dsimp only [B] <;> ring

theorem HasCubicExponent.full_element_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*(M*N)^ε*(M^(1/3 : ℝ)*N + M^ξ) := by
  obtain ⟨A,hA,hb⟩ := h.doubled (ε/2) (by positivity)
  let D : ℝ := 2 + 1/((ε/4)*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨(384*128^2 : ℝ)*A*D^2, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hlog := SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength_small_power (ε/4) (by positivity) M hM
  have hLP : (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 ≤ D^2*M^(ε/2) := by
    have hh := pow_le_pow_left₀ (by positivity) hlog 2
    rw [mul_pow, ← Real.rpow_mul_natCast hM0.le] at hh
    have he : (ε/4)*(2:ℕ) = ε/2 := by push_cast; ring
    rw [he] at hh
    exact hh
  have hMP : M^(ε/2) ≤ (M*N)^(ε/2) := Real.rpow_le_rpow hM0.le
    (by nlinarith) (by positivity)
  have hprod : (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 * (M*N)^(ε/2) ≤
      D^2*(M*N)^ε := by
    calc
      _ ≤ (D^2*M^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right hLP (Real.rpow_nonneg (by positivity) _)
      _ ≤ (D^2*(M*N)^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMP (sq_nonneg _))
          (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add (mul_pos hM0 hN0)]
        congr 2
        ring
  have he := elementSieveNorm_two_power_log ξ (ε/2) A M N hξ (by positivity) hA.le hM hN
    (fun X hX => hb X N hX hN)
  calc
    _ ≤ (384*128^2 : ℝ)*A*
        (SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
        (M*N)^(ε/2)*(M^(1/3 : ℝ)*N+M^ξ) := he
    _ = ((384*128^2 : ℝ)*A)*
        ((SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M*N)^(ε/2))*
        (M^(1/3 : ℝ)*N+M^ξ) := by ring
    _ ≤ ((384*128^2 : ℝ)*A)*(D^2*(M*N)^ε)*(M^(1/3 : ℝ)*N+M^ξ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)
    _ = _ := by ring

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
noncomputable section

lemma descendant_cross_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) :
    ((M/E)*(N/D))^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact mul_le_mul (div_le_self hM hE) (div_le_self hN hD) (by positivity) hM

lemma descendant_asymmetric_le (M N D E ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hED : E ≤ D) (hξ : 1 ≤ ξ) :
    (M/E)^(1-ξ)*(N/D)^(2*ξ-1) ≤ M^(1-ξ)*N^(2*ξ-1) := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hp : E^(ξ-1) ≤ D^(2*ξ-1) :=
    (Real.rpow_le_rpow hE0.le hED (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith))
  have hr : E^(ξ-1)/D^(2*ξ-1) ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hD0 _)).mpr hp
  have he : E^(1-ξ) = (E^(ξ-1))⁻¹ := by
    rw [← Real.rpow_neg hE0.le]
    congr 1
    ring
  calc
    _ = (M^(1-ξ)*N^(2*ξ-1))*(E^(ξ-1)/D^(2*ξ-1)) := by
      rw [Real.div_rpow hM.le hE0.le, Real.div_rpow hN.le hD0.le, he]
      simp only [div_eq_mul_inv, inv_inv]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hr

lemma descendant_loss_le (M N D E δ ε : ℝ) (hM : 1 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hED : E ≤ D) (hDN : D ≤ N)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    (M/E)^(-δ)*(N/D)^(3*δ+ε) ≤ N^(4*δ+ε) := by
  have hM0 : 0 < M := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hEM : E/M ≤ N := (div_le_self hE0.le hM).trans (hED.trans hDN)
  have hfirst : (M/E)^(-δ) ≤ N^δ := by
    rw [Real.rpow_neg (div_pos hM0 hE0).le, ← Real.inv_rpow (div_pos hM0 hE0).le, inv_div]
    exact Real.rpow_le_rpow (by positivity) hEM hδ
  have hsecond : (N/D)^(3*δ+ε) ≤ N^(3*δ+ε) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hN.le hD) (by positivity)
  calc
    _ ≤ N^δ*N^(3*δ+ε) := mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hN]
      congr 1
      ring

lemma descendant_unit_scale_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hDN : D ≤ N) :
    (M/E)*(2/(N/D)) ≤ 2*M := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hY : 1 ≤ N/D := (one_le_div hD0).mpr hDN
  have hr : 2/(N/D) ≤ 2 := div_le_self (by norm_num) hY
  calc
    _ ≤ M*2 := mul_le_mul (div_le_self hM hE) hr (by positivity) hM
    _ = _ := mul_comm _ _

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical
open SecondPassArithmetic SchwartzPlanePoisson CubicDyadicDecay
noncomputable section

theorem HasCubicExponent.frequencyCost_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1/2) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε : ℝ, 0 ≤ C → ∀ hε : 0 < ε,
      ∀ X Y : ℝ, 0 < X → 1 ≤ Y →
        frequencyCost C ε hε X Y ≤
          (X*(2/Y))*‖paperRadialFourier rowMajorant 0‖ +
          (2*C*DivisorBlockCauchy.divisorConstant ε hε*A) * Y^ε *
            (Y^(3*δ)*X^(-δ) * (decayConstant (1/3+δ)*(X*Y)^(2/3 : ℝ) +
              decayConstant (ξ+δ)*X^(1-ξ)*Y^(2*ξ-1))) := by
  obtain ⟨A,hA,hb⟩ := h.full_element_bound hξ δ hδ
  refine ⟨A,hA,?_⟩
  intro C ε hC hε X Y hX hY
  have hY0 : 0 < Y := by linarith
  have hs := sieve_poisson_bound (fun K => elementSieveNorm K Y) A X Y δ ξ hA.le hX hY0
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun K hK => elementSieveNorm_nonneg K Y)
    (fun K hK => by simpa only [mul_comm Y (K^(1/3 : ℝ))] using hb K Y hK hY)
  have hfac : 0 ≤ 2*C*DivisorBlockCauchy.divisorConstant ε hε*Y^ε := by
    have hp := (DivisorBlockCauchy.divisorConstant_pos ε hε).le
    positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  have he := add_le_add_left hh ((X*(2/Y))*‖paperRadialFourier rowMajorant 0‖)
  convert he using 1 <;> try dsimp only [frequencyCost, frequencyMajorant]
  all_goals first | rfl | ring

theorem frequencyCost_descendant_of_bound (C ε A δ ξ M N d e : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hα3 : 1/3+δ < 3) (hβ3 : ξ+δ < 3)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d) (hdN : d ≤ N)
    (hb : frequencyCost C ε hε (M/e) (N/d) ≤
      ((M/e)*(2/(N/d)))*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*DivisorBlockCauchy.divisorConstant ε hε*A)*(N/d)^ε*
        ((N/d)^(3*δ)*(M/e)^(-δ) *
          (decayConstant (1/3+δ)*((M/e)*(N/d))^(2/3 : ℝ) +
            decayConstant (ξ+δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)))) :
    frequencyCost C ε hε (M/e) (N/d) ≤
      2*M*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*DivisorBlockCauchy.divisorConstant ε hε*A)*N^ε*
        (N^(3*δ)*M^(-δ) *
          (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
            decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1))) := by
  have hd : 1 ≤ d := he.trans hed
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hp := (decayConstant_pos (1/3+δ) (by linarith) hα3).le
  have hq := (decayConstant_pos (ξ+δ) (by linarith) hβ3).le
  have henv := poisson_envelope_descendant_le M N e d δ ξ
    (decayConstant (1/3+δ)) (decayConstant (ξ+δ)) hM hN he hed hδ hξ hp hq
  have hny : (N/d)^ε ≤ N^ε := Real.rpow_le_rpow (by positivity) (div_le_self hN.le hd) hε.le
  have hfac : 0 ≤ 2*C*DivisorBlockCauchy.divisorConstant ε hε*A := by
    have hp := (DivisorBlockCauchy.divisorConstant_pos ε hε).le
    positivity
  apply hb.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (descendant_unit_scale_le M N d e hM.le hN hd he hdN) (norm_nonneg _)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hny hfac
    · exact henv
    · positivity
    · positivity

lemma poisson_envelope_absorb (M N δ ε ξ H Z P Q : ℝ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    2*M*Z + H*N^ε*(N^(3*δ)*M^(-δ)*
      (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1))) ≤
        (2*Z+H*(P+Q))*N^(3*δ+ε)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let X := (M*N)^(2/3 : ℝ)
  let Y := M^(1-ξ)*N^(2*ξ-1)
  let S := M+X+Y
  have hX : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hshape : P*X+Q*Y ≤ (P+Q)*S := by
    dsimp only [S]
    nlinarith [mul_nonneg hP hM0.le, mul_nonneg hQ hM0.le, mul_nonneg hP hY, mul_nonneg hQ hX]
  have hsmall : M^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hloss : 1 ≤ N^(3*δ+ε) := Real.one_le_rpow hN (by positivity)
  have hunit : 2*M*Z ≤ 2*Z*N^(3*δ+ε)*S := by
    have hmS : M ≤ S := by dsimp [S]; linarith
    calc
      _ = 2*Z*M := by ring
      _ ≤ 2*Z*S := mul_le_mul_of_nonneg_left hmS (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*Z) hS) (sub_nonneg.mpr hloss)]
  have htail : H*N^ε*(N^(3*δ)*M^(-δ)*(P*X+Q*Y)) ≤
      H*(P+Q)*N^(3*δ+ε)*S := by
    have hs : M^(-δ)*(P*X+Q*Y) ≤ (P+Q)*S :=
      (mul_le_of_le_one_left (by positivity) hsmall).trans hshape
    have hpow : N^ε*N^(3*δ) = N^(3*δ+ε) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      _ = H*(N^ε*N^(3*δ))*(M^(-δ)*(P*X+Q*Y)) := by ring
      _ ≤ H*(N^ε*N^(3*δ))*((P+Q)*S) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [hpow]; ring
  have hh := add_le_add hunit htail
  convert hh using 1 <;> (try dsimp only [S,X,Y]) <;> first | rfl | ring

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  
open SchwartzPlanePoisson.CanonicalQuadraticSieve FiniteSieveRestriction
noncomputable section
local notation "O" => Eisenstein.O

def cubicColumnLabel {n : Type*} (cols : n → Ideal O) (N : ℝ) (j : n) :
    Fin (columnDyadicLength N + 1) := divisorDyadicLabel N (cols j)

abbrev CubicColumnShell {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (l : Fin (columnDyadicLength N + 1)) := {j : n // cubicColumnLabel cols N j = l}

lemma cubicColumnShell_bounds {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val/2 ≤ (Ideal.absNorm (cols j.val) : ℝ) ∧
      (Ideal.absNorm (cols j.val) : ℝ) ≤ (2 : ℝ)^l.val := by
  have hp : 1 ≤ (Ideal.absNorm (cols j.val) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (primaryIdealGenerator_ne_zero_ideal _ (hc j.val).2))
  have hb := divisorDyadicLabel_bounds N (cols j.val) hp (hn j.val)
  have hj := j.property
  change divisorDyadicLabel N (cols j.val) = l at hj
  rw [hj] at hb
  exact ⟨hb.1.le,hb.2⟩

lemma cubicColumnShell_scale_le {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val ≤ 2*N := by
  have hh := (cubicColumnShell_bounds cols N hc hn l j).1
  linarith [hn j.val]

lemma cubicColumnShell_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) :
    (∑ l : Fin (columnDyadicLength N + 1), ∑ j : CubicColumnShell cols N l, ‖a j.val‖^2) =
      ∑ j, ‖a j‖^2 := Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => ‖a j‖^2)

theorem cubic_energy_column_shells {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) (R : Finset O) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      (columnDyadicLength N + 1 : ℝ) *
        ∑ l : Fin (columnDyadicLength N + 1), ∑ z ∈ R,
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z * a j.val‖^2 := by
  have hp (z : O) : ‖∑ j, cubicRow (cols j) z*a j‖^2 ≤
      (columnDyadicLength N + 1 : ℝ)*∑ l : Fin (columnDyadicLength N + 1),
        ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 := by
    rw [← Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => cubicRow (cols j) z*a j)]
    calc
      _ ≤ (∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
          (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ))
            (fun l : Fin (columnDyadicLength N + 1) =>
              ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖))
  calc
    _ ≤ ∑ z ∈ R, (columnDyadicLength N + 1 : ℝ)*
        ∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 :=
      Finset.sum_le_sum (fun z hz => hp z)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss  SchwartzPlanePoisson.CanonicalQuadraticSieve
open  SecondPassArithmetic SchwartzPlanePoisson
open CubicDyadicDecay
noncomputable section
local notation "O" => Eisenstein.O

theorem HasCubicExponent.annular_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (M N : ℝ), 1 ≤ M → 1 ≤ N → ∀ (cols : n → Ideal O), Function.Injective cols →
      (∀ j, Admissible (cols j)) →
      (∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      ∀ (a : n → ℂ) (R : Finset O),
        (∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) →
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z*a j‖^2) ≤
          K*N^(6*θ)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1))*∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hcf⟩ := cubic_common_factor_frequency_bound
  obtain ⟨A,hA,hfb⟩ := h.frequencyCost_bound hξ hξ2 θ hθ hθsmall
  let Z := ‖paperRadialFourier rowMajorant 0‖
  let P := decayConstant (1/3+θ)
  let Q := decayConstant (ξ+θ)
  let H := 2*C*DivisorBlockCauchy.divisorConstant θ hθ*A
  let V := 1+2*Z+H*(P+Q)
  let Dv := DivisorBlockCauchy.divisorConstant θ hθ
  have hZ : 0 ≤ Z := norm_nonneg _
  have hP : 0 ≤ P := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hQ : 0 ≤ Q := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hH : 0 ≤ H := by
    dsimp [H]
    have hs := (DivisorBlockCauchy.divisorConstant_pos θ hθ).le
    positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hDv : 0 < Dv := DivisorBlockCauchy.divisorConstant_pos θ hθ
  refine ⟨V*Dv^2, by positivity, ?_⟩
  intro n _ _ M N hM hN cols hinj hc hcols a R hR
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let U := V*N^(4*θ)*S
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcost (D : Ideal O) (hD : D ∈ gcdPool cols) (E : Ideal O) (hE : E ∈ idealDivisors D) :
      frequencyCost C θ hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U := by
    have hc0 (j : n) : cols j ≠ 0 := primaryIdealGenerator_ne_zero_ideal _ (hc j).2
    have hD0 := gcdPool_ne_zero cols hc0 D hD
    have hDE := (mem_idealDivisors hD0).mp hE
    have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hDE
    have he1 : 1 ≤ (Ideal.absNorm E : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
    have hed : (Ideal.absNorm E : ℝ) ≤ (Ideal.absNorm D : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
        (map_dvd Ideal.absNorm hDE)
    have hdN := (columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D
      (gcdPool_subset_columnDivisorPool cols hc0 hD)).2
    have hd0 : 0 < (Ideal.absNorm D : ℝ) := by linarith
    have he0 : 0 < (Ideal.absNorm E : ℝ) := by linarith
    have hh := hfb C θ hC hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ))
      (div_pos hM0 he0) ((one_le_div hd0).mpr hdN)
    have hd := frequencyCost_descendant_of_bound C θ A θ ξ M N
      (Ideal.absNorm D) (Ideal.absNorm E) hC hθ hA.le hθ.le (by linarith)
      (by linarith) (by linarith) hM0 hN0 he1 hed hdN hh
    have hb := poisson_envelope_absorb M N θ θ ξ H Z P Q hM hN hθ.le hθ.le hH hZ hP hQ
    have hx : 3*θ+θ = 4*θ := by ring
    rw [hx] at hb
    apply (hd.trans hb).trans
    change (2*Z+H*(P+Q))*N^(4*θ)*S ≤ V*N^(4*θ)*S
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [V]; linarith) (Real.rpow_nonneg hN0.le _)) hS
  have henergy := (hcf θ hθ M N hM0 cols hinj hc hcols a R hR).trans
    (common_factor_uniform_cost C θ U M N hθ hU hN0.le cols hc (fun j => (hcols j).2) a hcost)
  have hp : N^(4*θ)*(N^θ)^2 = N^(6*θ) := by
    rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  calc
    _ ≤ U*(Dv*N^θ)^2*∑ j, ‖a j‖^2 := henergy
    _ = (V*Dv^2)*(N^(4*θ)*(N^θ)^2)*S*∑ j, ‖a j‖^2 := by dsimp [U]; ring
    _ = _ := by rw [hp]

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical
open Eisenstein CompletedGauss 
open SchwartzPlanePoisson.CanonicalQuadraticSieve (columnDyadicLength)
noncomputable section
local notation "O" => Eisenstein.O

lemma improved_shape_shell (M N Y ξ : ℝ) (hM : 0 < M) (hN : 0 < N) (hY : 0 ≤ Y)
    (hYN : Y ≤ 2*N) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    M+(M*Y)^(2/3 : ℝ)+M^(1-ξ)*Y^(2*ξ-1) ≤
      8*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hp : (2:ℝ)^(2/3 : ℝ) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (2/3 : ℝ)≤3)
    norm_num at hh ⊢
    exact hh
  have hq : (2:ℝ)^(2*ξ-1) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 2*ξ-1 ≤ 3 by linarith)
    norm_num at hh
    exact hh
  have hcross := Real.rpow_le_rpow (mul_nonneg hM.le hY)
    (mul_le_mul_of_nonneg_left hYN hM.le) (by norm_num : (0:ℝ)≤2/3)
  have hsec := Real.rpow_le_rpow hY hYN (show 0 ≤ 2*ξ-1 by linarith)
  rw [show M*(2*N) = 2*(M*N) by ring, Real.mul_rpow (by norm_num) (mul_pos hM hN).le] at hcross
  rw [Real.mul_rpow (by norm_num) hN.le] at hsec
  have hx := (hcross.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (mul_pos hM hN).le _)))
  have hy := mul_le_mul_of_nonneg_left
    (hsec.trans (mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hN.le _)))
      (Real.rpow_nonneg hM.le (1-ξ))
  nlinarith

lemma improved_loss_shell (N Y θ : ℝ) (hN : 0 ≤ N) (hY : 0 ≤ Y) (hYN : Y ≤ 2*N)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/2) : Y^(6*θ) ≤ 8*N^(6*θ) := by
  have hh := Real.rpow_le_rpow hY hYN (show 0 ≤ 6*θ by positivity)
  rw [Real.mul_rpow (by norm_num) hN] at hh
  have hp : (2:ℝ)^(6*θ) ≤ 8 := by
    have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 6*θ ≤ 3 by linarith)
    norm_num at he
    exact he
  exact hh.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN _))

theorem HasCubicExponent.full_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*N^(7*θ)*
        (M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  obtain ⟨K,hK,hb⟩ := h.annular_improved hξ hξ2 θ hθ hθsmall
  let D : ℝ := 2+1/(θ*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    positivity
  refine ⟨64*K*D, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let cols : idealRange N → Ideal O := fun j => j.val
  have hc (j : idealRange N) : Admissible (cols j) := (mem_idealRange.mp j.property).1
  have hn (j : idealRange N) : (Ideal.absNorm (cols j) : ℝ) ≤ N := (mem_idealRange.mp j.property).2
  let R := elementRange M
  have hR (z : O) (hz : z ∈ R) : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    ((mem_elementRange M z).mp hz).2
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  have hsector (l : Fin (columnDyadicLength N + 1)) :
      (∑ z ∈ R, ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2) ≤
        (64*K*N^(6*θ)*S)*∑ j : CubicColumnShell cols N l, ‖a j.val‖^2 := by
    by_cases hne : Nonempty (CubicColumnShell cols N l)
    · obtain ⟨j₀⟩ := hne
      have hYN := cubicColumnShell_scale_le cols N hc hn l j₀
      have hY1 : 1 ≤ (2:ℝ)^l.val := one_le_pow₀ (by norm_num)
      have hs := hb M ((2:ℝ)^l.val) hM hY1
        (fun j : CubicColumnShell cols N l => cols j.val)
        (fun j k he => Subtype.ext (Subtype.ext he)) (fun j => hc j.val)
        (fun j => cubicColumnShell_bounds cols N hc hn l j)
        (fun j => a j.val) R hR
      have hl := improved_loss_shell N ((2:ℝ)^l.val) θ hN0.le (by positivity) hYN hθ.le hθsmall.le
      have ht := improved_shape_shell M N ((2:ℝ)^l.val) ξ hM0 hN0 (by positivity) hYN
        (by linarith) hξ2
      apply hs.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hl hK.le) ht (by positivity) (by positivity)
      convert hh using 1; dsimp only [S]; ring
    · let : IsEmpty (CubicColumnShell cols N l) := not_nonempty_iff.mp hne
      simp
  have hsum := cubic_energy_column_shells cols N a R
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun l hl => hsector l)
  rw [← Finset.mul_sum, cubicColumnShell_energy cols N a] at hle
  have he := hsum.trans (mul_le_mul_of_nonneg_left hle (by positivity))
  have hlog := SchwartzPlanePoisson.CanonicalQuadraticSieve.columnDyadicLength_small_power θ hθ N hN
  have he' := he.trans (mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ (64*K*N^(6*θ)*S)*∑ j, ‖a j‖^2 by positivity))
  have hp : N^θ*N^(6*θ) = N^(7*θ) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val*a j‖^2) ≤ _
  apply he'.trans_eq
  calc
    _ = (64*K*D)*(N^θ*N^(6*θ))*S*∑ j, ‖a j‖^2 := by dsimp [D]; ring
    _ = _ := by rw [hp]

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace HeathBrownIteration

noncomputable section

def step (x : ℝ) : ℝ := (6 * x - 4) / (3 * x - 1)

theorem step_sub (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  have hd : 3 * x - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  unfold step
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

theorem step_gt {x : ℝ} (hx : (4 / 3 : ℝ) < x) :
    (4 / 3 : ℝ) < step x := by
  have h := step_sub x hx.le
  have hp : 0 < 2 * (x - 4 / 3) / (3 * x - 1) :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hx)) (by linarith)
  linarith

theorem step_error_le {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [step_sub x hx]
  apply (div_le_iff₀ (by linarith : 0 < 3 * x - 1)).mpr
  nlinarith [sq_nonneg (x - 4 / 3)]

theorem step_lt {x : ℝ} (hx : (4 / 3 : ℝ) < x) : step x < x := by
  have h := step_error_le hx.le
  linarith

def exponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => step (exponent n)

theorem exponent_bounds (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩

theorem exponent_error_le (n : ℕ) :
    exponent n - 4 / 3 ≤ (2 / 3 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    calc
      exponent (n + 1) - 4 / 3 ≤ (2 / 3 : ℝ) * (exponent n - 4 / 3) :=
        step_error_le (exponent_bounds n).1.le
      _ ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 / 3 : ℝ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem exists_exponent_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, exponent n < 4 / 3 + ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (2 / 3 : ℝ) ^ (n + 1) ≤ (2 / 3 : ℝ) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have he := exponent_error_le n
  linarith

theorem finite_improvement {P : ℝ → Prop} (hstart : P 2)
    (himprove : ∀ x : ℝ, (4 / 3 : ℝ) < x → x ≤ 2 → P x → P (step x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, (4 / 3 : ℝ) < x ∧ x ≤ 2 ∧ x < 4 / 3 + ε ∧ P x := by
  have hp (n : ℕ) : P (exponent n) := by
    induction n with
    | zero => exact hstart
    | succ n ih => exact himprove _ (exponent_bounds n).1 (exponent_bounds n).2 ih
  obtain ⟨n, hn⟩ := exists_exponent_lt hε
  exact ⟨exponent n, (exponent_bounds n).1, (exponent_bounds n).2, hn, hp n⟩

end

end HeathBrownIteration

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
open scoped BigOperators Classical
noncomputable section

def enlargementExponent (ξ : ℝ) : ℝ := (6*ξ-5)/(3*ξ-1)

lemma enlargement_bounds (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    1 ≤ enlargementExponent ξ ∧ enlargementExponent ξ ≤ HeathBrownIteration.step ξ := by
  have hd : 0 < 3*ξ-1 := by linarith
  constructor
  · unfold enlargementExponent
    apply (one_le_div hd).mpr
    linarith
  · unfold enlargementExponent HeathBrownIteration.step
    exact div_le_div_of_nonneg_right (by linarith) hd.le

lemma enlargement_cross_identity (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    (enlargementExponent ξ+1)*(2/3 : ℝ) = HeathBrownIteration.step ξ := by
  have hd : 3*ξ-1 ≠ 0 := by linarith
  unfold enlargementExponent HeathBrownIteration.step
  apply (eq_div_iff hd).mpr
  have hc := div_mul_cancel₀ (6*ξ-5) hd
  nlinarith [hc]

lemma enlargement_secondary_identity (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    enlargementExponent ξ*(1-ξ)+(2*ξ-1) = HeathBrownIteration.step ξ := by
  have hd : 3*ξ-1 ≠ 0 := by linarith
  unfold enlargementExponent HeathBrownIteration.step
  apply (eq_div_iff hd).mpr
  have hc := div_mul_cancel₀ (6*ξ-5) hd
  nlinarith [hc]

theorem enlarged_improved_shape (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    let T := max M (N^(enlargementExponent ξ))
    T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤
      3*(M+N^(HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ)) := by
  let α := enlargementExponent ξ
  let β := HeathBrownIteration.step ξ
  let T := max M (N^α)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hαβ : α ≤ β := (enlargement_bounds ξ hξ).2
  have hNb : 0 ≤ N^β := Real.rpow_nonneg hN0.le _
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have ht : T ≤ M+N^β := by
    apply max_le
    · exact le_add_of_nonneg_right hNb
    · exact (Real.rpow_le_rpow_of_exponent_le hN hαβ).trans (le_add_of_nonneg_left hM0.le)
  have hnx : (N^α*N)^(2/3 : ℝ) = N^β := by
    conv_lhs => arg 1; arg 2; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN0, ← Real.rpow_mul hN0.le, enlargement_cross_identity ξ hξ]
  have htc : (T*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ)+N^β := by
    by_cases hm : M ≤ N^α
    · dsimp only [T]
      rw [max_eq_right hm, hnx]
      exact le_add_of_nonneg_left hcross
    · dsimp only [T]
      rw [max_eq_left (le_of_not_ge hm)]
      exact le_add_of_nonneg_right hNb
  have hts : T^(1-ξ)*N^(2*ξ-1) ≤ N^β := by
    have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 α)
      (le_max_right M (N^α)) (show 1-ξ ≤ 0 by linarith)
    calc
      _ ≤ (N^α)^(1-ξ)*N^(2*ξ-1) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN0.le _)
      _ = N^β := by
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, enlargement_secondary_identity ξ hξ]
  change T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤ 3*(M+N^β+(M*N)^(2/3 : ℝ))
  linarith

theorem HasCubicExponent.improve {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) < ξ) (hξ2 : ξ ≤ 2) :
    HasCubicExponent (HeathBrownIteration.step ξ) := by
  intro ε hε
  let θ := min (ε/14) (1/4 : ℝ)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθsmall : θ < 1/2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθε : 7*θ ≤ ε := by
    have hh : θ ≤ ε/14 := min_le_left _ _
    linarith
  obtain ⟨C,hC,hb⟩ := h.full_improved hξ.le hξ2 θ hθ hθsmall
  refine ⟨3*C, by positivity, ?_⟩
  intro M N hM hN
  let T := max M (N^(enlargementExponent ξ))
  have hT : 1 ≤ T := hM.trans (le_max_left _ _)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hp : N^(7*θ) ≤ (M*N)^ε :=
    (Real.rpow_le_rpow_of_exponent_le hN hθε).trans
      (Real.rpow_le_rpow hN0.le (by nlinarith) hε.le)
  have ht := enlarged_improved_shape M N ξ hM hN hξ.le
  have hshape : 0 ≤ M+N^(HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ) := by positivity
  calc
    _ ≤ sieveNorm T N := sieveNorm_mono (le_max_left _ _) le_rfl
    _ ≤ elementSieveNorm T N := sieveNorm_le_elementSieveNorm T N
    _ ≤ C*N^(7*θ)*(T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1)) := hb T N hT hN
    _ ≤ C*N^(7*θ)*(3*(M+N^(HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ C*(M*N)^ε*(3*(M+N^(HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (by positivity)
    _ = _ := by ring

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FiniteSieveOperator UniqueFactorizationMonoid FirstPassCubeLabels
open scoped BigOperators Classical SchwartzMap
namespace CubicSieve
noncomputable section

theorem hasCubicExponent_four_thirds : HasCubicExponent (4/3 : ℝ) := by
  intro ε hε
  obtain ⟨ξ, hξ, hξ2, hξε, hx⟩ := HeathBrownIteration.finite_improvement
    hasCubicExponent_initial (fun x hx hx2 hp => hp.improve hx hx2)
    (show 0 < ε/2 by positivity)
  obtain ⟨C,hC,hb⟩ := hx (ε/2) (by positivity)
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hMN : 0 < M*N := mul_pos hM0 hN0
  have hp : 1 ≤ N^(ε/2) := Real.one_le_rpow hN (by positivity)
  have hNpow : N^ξ ≤ N^(4/3 : ℝ)*N^(ε/2) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN hξε.le
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg hMN.le _
  have hs : M+N^ξ+(M*N)^(2/3 : ℝ) ≤
      N^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := by
    nlinarith [mul_nonneg hM0.le (sub_nonneg.mpr hp),
      mul_nonneg hcross (sub_nonneg.mpr hp)]
  have hnp : N^(ε/2) ≤ (M*N)^(ε/2) :=
    Real.rpow_le_rpow hN0.le (by nlinarith) (by positivity)
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^ξ+(M*N)^(2/3 : ℝ)) := hb M N hM hN
    _ ≤ C*(M*N)^(ε/2)*(N^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnp (by positivity)) (by positivity)
    _ = _ := by
      have he : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add hMN]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := by ring
        _ = _ := by rw [he]

lemma four_thirds_le_cross (M N : ℝ) (_hM : 1 ≤ M) (hN : 1 ≤ N) (hNM : N ≤ M) :
    N^(4/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
  have hN0 : 0 ≤ N := by linarith
  calc
    N^(4/3 : ℝ) = (N*N)^(2/3 : ℝ) := by
      rw [Real.mul_rpow hN0 hN0, ← Real.rpow_add (by linarith : 0 < N)]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hN0 hN0)
      (mul_le_mul_of_nonneg_right hNM hN0) (by norm_num)

theorem sieveNorm_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C*(M*N)^ε*(M+N+(M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := hasCubicExponent_four_thirds ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (mul_nonneg hM0 hN0) _
  by_cases hNM : N ≤ M
  · have hh := four_thirds_le_cross M N hM hN hNM
    calc
      _ ≤ C*(M*N)^ε*(M+N^(4/3 : ℝ)+(M*N)^(2/3 : ℝ)) := hb M N hM hN
      _ ≤ C*(M*N)^ε*(2*(M+N+(M*N)^(2/3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  · have hMN := le_of_not_ge hNM
    have hh := four_thirds_le_cross N M hN hM hMN
    have hs : N+M^(4/3 : ℝ)+(N*M)^(2/3 : ℝ) ≤
        2*(M+N+(M*N)^(2/3 : ℝ)) := by
      rw [mul_comm N M] at hh ⊢
      linarith
    calc
      _ = sieveNorm N M := sieveNorm_reciprocity M N
      _ ≤ C*(N*M)^ε*(N+M^(4/3 : ℝ)+(N*M)^(2/3 : ℝ)) := hb N M hN hM
      _ ≤ C*(N*M)^ε*(2*(M+N+(M*N)^(2/3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [mul_comm N M]; ring

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CubicSieve

/-- The full residue Gauss sum restricts to units because the cubic row vanishes elsewhere. -/
theorem gaussTwo_eq_normalizedCubicUnitGauss (I : Ideal O)
    (hI : primaryIdealGenerator I ≠ 0) :
    gaussTwo I hI = normalizedCubicUnitGauss (primaryIdealGenerator I) := by
  unfold gaussTwo normalizedCubicUnitGauss
  congr 1
  let c := primaryIdealGenerator I
  have hspan : Ideal.span {c} = I := (primaryIdealGenerator_spec I hI).1
  let f (r : O ⧸ Ideal.span {c}) : ℂ :=
    ringComplex (symbol (principalResidueRep c r) c) *
      residueAdditive (3 * 1) c (principalResidueRep c r)
  have hunit : (∑' r : CubicUnitResidue c, f r.val) = ∑' r : O ⧸ Ideal.span {c}, f r := by
    apply tsum_subtype_eq_of_support_subset (s := {r | IsUnit r})
    intro r hr
    have hn : ringComplex (symbol (principalResidueRep c r) c) ≠ 0 :=
      left_ne_zero_of_mul hr
    have hm := idealSymbol_cube_mask I (principalResidueRep c r) hI
    have hc : IsCoprime I (Ideal.span {principalResidueRep c r}) := by
      by_contra h
      rw [if_neg h] at hm
      have hn' : ringComplex (idealSymbol I (principalResidueRep c r)) ≠ 0 := by
        simpa only [symbol, hspan] using hn
      exact (pow_ne_zero 3 hn') hm
    have he : IsCoprime c (principalResidueRep c r) :=
      (Ideal.isCoprime_span_singleton_iff _ _).mp (hspan.symm ▸ hc)
    change IsUnit r
    simpa only [principalResidueRep_spec] using
      (isUnit_quotient_span_iff c (principalResidueRep c r)).mpr he
  change (∑' r : O ⧸ Ideal.span {c},
    cubicRow I (qrep r) * residueTraceQuotientChar 1 c hI r) =
    ∑' r : CubicUnitResidue c, f r.val
  rw [hunit]
  apply tsum_congr
  intro r
  have hr : c ∣ qrep r - principalResidueRep c r := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq.mp
    rw [mk_qrep, principalResidueRep_spec]
  have ht := residueTraceQuotientChar_mk 1 c hI (principalResidueRep c r)
  rw [principalResidueRep_spec] at ht
  rw [cubicRow_congr I hI _ _ hr, ht]
  simp only [f, cubicRow, symbol, hspan]

end CubicSieve

namespace CompletedGauss

/-- The squarefree coefficient uses the same primitive trace normalization as the physical row. -/
theorem squarefreeGaussCoefficient_eq (I : Ideal O) (hs : Squarefree I)
    (hI : primaryIdealGenerator I ≠ 0) :
    squarefreeGaussCoefficient I =
      star (angularFactor (primaryIdealGenerator I)) * CubicSieve.gaussTwo I hI := by
  rw [squarefreeGaussCoefficient, if_pos hs, CubicSieve.gaussTwo_eq_normalizedCubicUnitGauss]

end CompletedGauss

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
