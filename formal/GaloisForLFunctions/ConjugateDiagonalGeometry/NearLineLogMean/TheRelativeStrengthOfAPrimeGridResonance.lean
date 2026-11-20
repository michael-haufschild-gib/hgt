import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeGridMoebiusMeans
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Limiting strength of a prime-grid resonance

A squarefree integer either omits p or contains it exactly once. The
two portions of the harmonic diagonal are consequently the same
coprime sum at cutoffs N and N/p, with the second divided by p.
The terminal interval costs at most 1+log p. Thus the relative
prime resonance approaches a fixed, strictly negative Fourier
coefficient independent of the density constant of the squarefrees.
-/

noncomputable section
open Finset Complex Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.MultiscaleMollifiedZetaField
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram

private def terms (N : ℕ) := (Icc 1 N).filter Squarefree
private def freeTerms (p N : ℕ) := (terms N).filter (fun d => p.Coprime d)
private def freeMass (p N : ℕ) : ℝ := ∑ d ∈ freeTerms p N, (d:ℝ)⁻¹

/-- Exact diagonal of the critical Möbius polynomial. -/
def squarefreeDiagonal (N : ℕ) : ℝ := ∑ n ∈ terms N, (n:ℝ)⁻¹

private theorem mobius_sq_indicator (n : ℕ) :
    mobiusRealCoefficient n^2 = if Squarefree n then 1 else 0 := by
  rw [mobiusRealCoefficient,←Int.cast_pow,ArithmeticFunction.moebius_sq]
  split <;> norm_num

private theorem diagonal_eq (N : ℕ) :
    (∑ n ∈ Icc 1 N, mobiusRealCoefficient n^2/n) = squarefreeDiagonal N := by
  simp only [squarefreeDiagonal,terms,sum_filter,mobius_sq_indicator,ite_div,one_div,zero_div]

private theorem geometric_split (p N : ℕ) (hp : p.Prime) :
    squarefreeDiagonal N = freeMass p N + freeMass p (N/p)/(p:ℝ) := by
  let T := (terms N).filter fun d => ¬ p.Coprime d
  have he : T = (freeTerms p (N/p)).image (p*·) := by
    ext d
    constructor
    · intro hd
      obtain ⟨ht,hn⟩ := mem_filter.mp hd
      obtain ⟨hI,hs⟩ := mem_filter.mp ht
      obtain ⟨h1,hN⟩ := mem_Icc.mp hI
      obtain ⟨e,rfl⟩ := (not_not.mp (fun h => hn (hp.coprime_iff_not_dvd.mpr h)) : p ∣ d)
      obtain ⟨hc,_,he⟩ := Nat.squarefree_mul_iff.mp hs
      refine mem_image.mpr ⟨e,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,?_⟩,he⟩,hc⟩,rfl⟩
      · exact Nat.pos_of_ne_zero fun hz => by simp [hz] at h1
      · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa only [mul_comm] using hN)
    · intro hd
      obtain ⟨e,he,rfl⟩ := mem_image.mp hd
      obtain ⟨ht,hc⟩ := mem_filter.mp he
      obtain ⟨hI,hs⟩ := mem_filter.mp ht
      obtain ⟨h1,hcut⟩ := mem_Icc.mp hI
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hp.pos h1,?_⟩,
        Nat.squarefree_mul_iff.mpr ⟨hc,hp.squarefree,hs⟩⟩,?_⟩
      · simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hcut
      · exact fun h => hp.coprime_iff_not_dvd.mp h (dvd_mul_right p e)
  have h := sum_filter_add_sum_filter_not (terms N) (p.Coprime ·) (fun n : ℕ => (n:ℝ)⁻¹)
  change freeMass p N+(∑ n ∈ T, (n:ℝ)⁻¹) = squarefreeDiagonal N at h
  rw [←h,he,sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hp.pos he)]
  congr 1
  rw [freeMass,sum_div]
  apply sum_congr rfl
  intro d _
  rw [Nat.cast_mul,mul_inv_rev,div_eq_mul_inv]

private theorem terminal_mass {p : ℕ} (hp : p.Prime) (N : ℕ) :
    0 ≤ freeMass p N-freeMass p (N/p) ∧
    freeMass p N-freeMass p (N/p) ≤ 1+Real.log p := by
  let K := N/p
  have hk : K ≤ N := Nat.div_le_self ..
  have hsub : freeTerms p K ⊆ freeTerms p N := by
    intro d hd
    simpa only [freeTerms,terms,mem_filter,mem_Icc] using
      (show ((1 ≤ d ∧ d ≤ N) ∧ Squarefree d) ∧ p.Coprime d from by
        obtain ⟨⟨⟨h1,hk'⟩,hs⟩,hc⟩ := (show ((1 ≤ d ∧ d ≤ K) ∧ Squarefree d) ∧ p.Coprime d by
          simpa only [freeTerms,terms,mem_filter,mem_Icc] using hd)
        exact ⟨⟨⟨h1,hk'.trans hk⟩,hs⟩,hc⟩)
  let V := freeTerms p N \ freeTerms p K
  have hsum : freeMass p N-freeMass p K=∑ d ∈ V, (d:ℝ)⁻¹ := by
    have h := sum_sdiff hsub (f:=fun d : ℕ => (d:ℝ)⁻¹)
    linarith only [show (∑ d ∈ V, (d:ℝ)⁻¹)+freeMass p K=freeMass p N from h]
  rw [show freeMass p N-freeMass p (N/p)=∑ d ∈ V, (d:ℝ)⁻¹ from hsum]
  refine ⟨sum_nonneg fun _ _ => by positivity,?_⟩
  have hV : V ⊆ Ioc K N := by
    intro d hd
    obtain ⟨hd,hk'⟩ := mem_sdiff.mp hd
    simp only [freeTerms,terms,mem_filter,mem_Icc] at hd hk'
    exact mem_Ioc.mpr ⟨lt_of_not_ge fun h => hk' ⟨⟨⟨hd.1.1.1,h⟩,hd.1.2⟩,hd.2⟩,hd.1.1.2⟩
  apply (sum_le_sum_of_subset_of_nonneg hV fun _ _ _ => by positivity).trans
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [K,Real.log_nonneg (Nat.one_le_cast.mpr hp.pos)]
  have hhar (n : ℕ) : (harmonic n:ℝ) = ∑ d ∈ Ioc 0 n, (d:ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have hsplit := sum_Ioc_consecutive (fun d : ℕ => (d:ℝ)⁻¹) (Nat.zero_le K) hk
  rw [←hhar,←hhar] at hsplit
  have hn : (N:ℝ) ≤ (K+1:ℝ)*p := by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul hp.pos).mp (Nat.lt_succ_self K)).le
  have hk' : (0:ℝ) < K+1 := by positivity
  have hp' : 0 < (p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hl := Real.log_le_log (Nat.cast_pos.mpr hN) hn
  rw [Real.log_mul hk'.ne' hp'.ne'] at hl
  linarith only [hsplit,harmonic_le_one_add_log N,log_add_one_le_harmonic K,hl]

private theorem scale_prime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    primitiveCubicScaleWeight 0 N p 1 = freeMass p (N/p) := by
  have he : ratioScales N p 1 = Icc 1 (N/p) := by
    ext d
    simp only [ratioScales,mem_filter,mem_Icc,mul_one,←Nat.le_div_iff_mul_le hp.pos]
    have hk := Nat.div_le_self N p
    omega
  rw [primitiveCubicScaleWeight,he,freeMass,freeTerms,terms,sum_filter,sum_filter]
  apply sum_congr rfl
  intro d _
  simp only [Nat.coprime_one_right,and_true,sub_zero,Real.rpow_neg_one,mobius_sq_indicator]
  by_cases hs : Squarefree d <;> by_cases hc : p.Coprime d <;> simp [hs,hc,Nat.coprime_comm d p]

private theorem prime_atom {p : ℕ} (hp : p.Prime) (N : ℕ) :
    atom N p 1 = -(freeMass p (N/p))/Real.sqrt p := by
  rw [atom,scale_prime hp]
  simp only [coeff,mobiusRealCoefficient,ArithmeticFunction.moebius_apply_prime hp,Int.cast_neg,
    Int.cast_one,ArithmeticFunction.moebius_apply_one,Nat.cast_one,Real.sqrt_one,div_one,mul_one]
  ring

/-- The difference between the limiting relative amplitude times the
actual diagonal and the observed prime amplitude is one signed terminal
interval, uniformly bounded at fixed p. -/
theorem prime_resonance_amplitude {p : ℕ} (hp : p.Prime) (N : ℕ) :
    let x := Real.sqrt p/((p:ℝ)+1)
    0 ≤ x*squarefreeDiagonal N+atom N p 1 ∧
      x*squarefreeDiagonal N+atom N p 1 ≤ x*(1+Real.log p) := by
  intro x
  have hp' : 0 < (p:ℝ) := Nat.cast_pos.mpr hp.pos
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have he : x*squarefreeDiagonal N+atom N p 1=x*(freeMass p N-freeMass p (N/p)) := by
    rw [geometric_split p N hp,prime_atom hp]
    dsimp only [x]
    have alg (a b z : ℝ) (hz : 0 < z) :
        z/(z^2+1)*(a+b/z^2)+(-b)/z = z/(z^2+1)*(a-b) := by
      field_simp
      ring
    simpa only [Real.sq_sqrt hp'.le] using
      alg (freeMass p N) (freeMass p (N/p)) _ (Real.sqrt_pos.mpr hp')
  rw [he]
  exact ⟨mul_nonneg hx (terminal_mass hp N).1,mul_le_mul_of_nonneg_left (terminal_mass hp N).2 hx⟩

private theorem atom_swap (N a b : ℕ) : atom N a b=atom N b a := by
  rw [atom,atom,mul_comm (coeff a) (coeff b)]
  congr 1
  have h : ratioScales N a b=ratioScales N b a := by
    ext d; simp only [ratioScales,mem_filter,and_comm (d*a ≤ N)]
  simp only [primitiveCubicScaleWeight,h,and_comm (Nat.Coprime _ a)]

private theorem diagonal_diverges : Tendsto squarefreeDiagonal atTop atTop := by
  have h (N : ℕ) : Real.log ((N:ℝ)+1)/2 ≤ squarefreeDiagonal N := by
    have H := sum_inv_le_two_mul_sum_inv_squarefree N
    have hh := log_add_one_le_harmonic N
    rw [harmonic_eq_sum_Icc] at hh
    push_cast at hh
    simpa only [one_div,terms,squarefreeDiagonal] using
      (show Real.log ((N:ℝ)+1)/2 ≤ ∑ d ∈ (Icc 1 N).filter Squarefree, (d:ℝ)⁻¹ by
        simp only [one_div] at H
        linarith only [hh,H])
  have ht : Tendsto (fun N : ℕ => Real.log ((N:ℝ)+1)/2) atTop atTop :=
    (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right atTop (1:ℝ)
      tendsto_natCast_atTop_atTop)).atTop_div_const (by norm_num)
  exact tendsto_atTop_mono h ht

/-- Exact arithmetic normalization of the directed atom as the cutoff
grows. The two opposite directions each have this same limiting ratio. -/
theorem prime_resonance_relative_limit {p : ℕ} (hp : p.Prime) :
    Tendsto (fun N => atom N p 1/squarefreeDiagonal N) atTop
      (𝓝 (-(Real.sqrt p/((p:ℝ)+1)))) := by
  let x := Real.sqrt p/((p:ℝ)+1)
  let C := x*(1+Real.log p)
  have hz : Tendsto (fun N => C/squarefreeDiagonal N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop diagonal_diverges
  have he : Tendsto (fun N => x+atom N p 1/squarefreeDiagonal N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hz
    filter_upwards [diagonal_diverges.eventually_gt_atTop 0] with N hN
    have h := prime_resonance_amplitude hp N
    change 0 ≤ x*squarefreeDiagonal N+atom N p 1 ∧ x*squarefreeDiagonal N+atom N p 1 ≤ C at h
    rw [show x+atom N p 1/squarefreeDiagonal N =
        (x*squarefreeDiagonal N+atom N p 1)/squarefreeDiagonal N by field_simp,
      Real.norm_eq_abs,abs_of_nonneg (div_nonneg h.1 hN.le)]
    exact div_le_div_of_nonneg_right h.2 hN.le
  simpa only [add_sub_cancel_left,zero_sub] using he.sub_const x

/-- For each sufficiently long polynomial the entire prime-grid limit
is its diagonal plus a single cosine. After division by the diagonal
that cosine has the explicit amplitude 2√p/(p+1). -/
theorem normalized_prime_grid_profile (p : Nat.Primes) (t : ℝ) :
    ∃ V : ℕ → ℝ, (∀ N ≥ p.val,
      Tendsto (fun r : ℕ => (binomialHeightMean (2*Real.pi/Real.log p.val)^r)
        (fun x => ‖moebiusPoly N (linePoint x)‖^2) t) atTop (𝓝 (V N))) ∧
      Tendsto (fun N => V N/squarefreeDiagonal N) atTop
        (𝓝 (1-(2*Real.sqrt p.val/((p.val:ℝ)+1))*Real.cos (Real.log p.val*t))) := by
  let c := Real.cos (Real.log p.val*t)
  let V (N : ℕ) := squarefreeDiagonal N+2*atom N p.val 1*c
  refine ⟨V,fun N hN => ?_,?_⟩
  · have hp₁ := p.property.one_lt
    have hmem : (p.val,1) ∈ primitiveRatioPairs N ∧ (1,p.val) ∈ primitiveRatioPairs N := by
      simp only [primitiveRatioPairs,mem_filter,mem_product,mem_Icc,Nat.coprime_one_left,
        Nat.coprime_one_right,true_and]
      omega
    have hpair : (primitiveRatioPairs N).filter (fun q => q=(p.val,1) ∨ q=(1,p.val)) =
        {(p.val,1),(1,p.val)} := by
      ext q
      simp only [mem_filter,mem_insert,mem_singleton]
      exact ⟨And.right,fun h => ⟨h.elim (fun he => he ▸ hmem.1) (fun he => he ▸ hmem.2),h⟩⟩
    have hne : (p.val,1) ≠ (1,p.val) := fun h => hp₁.ne' (congrArg Prod.fst h)
    have he := prime_grid_binomial_spectrum N p t
    rw [hpair,sum_pair hne,diagonal_eq,atom_swap N 1 p.val] at he
    simpa only [Nat.cast_one,Real.log_one,sub_zero,zero_sub,neg_mul,Real.cos_neg,V,c,
      two_mul,add_mul] using he
  · have hlim := (prime_resonance_relative_limit p.property).const_mul (2:ℝ) |>.mul_const c
    have hh := hlim.const_add (1:ℝ)
    have hv : 1-(2*Real.sqrt p.val/((p.val:ℝ)+1))*Real.cos (Real.log p.val*t) =
        1+2*(-(Real.sqrt p.val/((p.val:ℝ)+1)))*c := by dsimp only [c]; ring
    rw [hv]
    apply hh.congr'
    filter_upwards [diagonal_diverges.eventually_gt_atTop 0] with N hn
    dsimp only [V]
    field_simp
    <;> ring

#print axioms prime_resonance_amplitude
#print axioms normalized_prime_grid_profile

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.MoebiusGram
