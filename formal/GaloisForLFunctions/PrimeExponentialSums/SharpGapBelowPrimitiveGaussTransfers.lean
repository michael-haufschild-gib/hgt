import GaloisForLFunctions.PrimeExponentialSums.PrincipalRamanujanTransferOnTheDisk
import GaloisForLFunctions.PrimeExponentialSums.ConductorShellOfTheLocalGaussTransfer

/-!
# An isolated primitive value in the Gauss transfer

At a prime power the squared transfer has the full value of the modulus
for every primitive character. Every imprimitive character has normalized
squared transfer at most 8/9; a nonprincipal imprimitive character has
at most 1/2. The sharp gap survives multiplication over prime powers.
-/

noncomputable section
open Finset RHTower
open scoped Classical
namespace GaloisForLFunctions.PrimeExponentialSums.GaussGap

def readout (p : Nat.Primes) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) :=
  ∑' v : ℕ, GaussShell.coeff N χ (p.val^v)*(z/p.val)^v

private instance primeNeZero (p : Nat.Primes) : NeZero p.val := ⟨p.property.ne_zero⟩

theorem principal_value (p : Nat.Primes) (e : ℕ) {z : ℂ} (hz : ‖z‖≤1) :
    readout p (p.val^(e+1)) 1 z = PrincipalRamanujan.transfer p.val e z := by
  have hp : (1 : ℝ)<p.val := by exact_mod_cast p.property.one_lt
  apply HasSum.tsum_eq
  apply (PrincipalRamanujan.hasSum_transfer p e (hz.trans_lt hp)).congr_fun
  intro v
  congr 1
  rw [cglRamanujanAdditiveSum_eq_indicator]
  unfold cglRamanujanAdditiveSumIndicator GaussShell.coeff
  refine sum_congr rfl fun x _ => ?_
  by_cases hu : IsUnit x
  · simp [cglUnitResidueIndicator,hu,MulChar.one_apply hu,mul_comm]
  · simp [cglUnitResidueIndicator,hu,MulChar.map_nonunit _ hu]

private theorem lifted_value (p : Nat.Primes) (j k N : ℕ) [NeZero N]
    (hN : N=p.val^(j+1)*p.val^k) (hd : p.val^(j+1)∣N)
    (ψ : DirichletCharacter ℂ (p.val^(j+1))) (hψ : ψ.IsPrimitive) (z : ℂ) :
    readout p N (DirichletCharacter.changeLevel hd ψ) z = gaussSum ψ ZMod.stdAddChar*z^k := by
  subst N
  exact (GaussShell.hasSum_monomial p j k ψ hψ z).tsum_eq

/-- A nonprincipal character has a single conductor loss k, including k=0
for primitive characters. Its norm is independent of the argument of z. -/
theorem nonprincipal_shape (p : Nat.Primes) (e : ℕ)
    (χ : DirichletCharacter ℂ (p.val^(e+1))) (hn : χ≠1) (z : ℂ) :
    ∃ j k : ℕ, j+1+k=e+1 ∧ χ.conductor=p.val^(j+1) ∧
      ‖readout p (p.val^(e+1)) χ z‖^2=(p.val : ℝ)^(j+1)*(‖z‖^k)^2 := by
  obtain ⟨d,hd,ψ,hψ,he,hc⟩ :
      ∃ d : ℕ, ∃ hd : d∣p.val^(e+1), ∃ ψ : DirichletCharacter ℂ d,
        ψ.IsPrimitive ∧ DirichletCharacter.changeLevel hd ψ=χ ∧ χ.conductor=d :=
    ⟨_,χ.conductor_dvd_level,χ.primitiveCharacter,χ.primitiveCharacter_isPrimitive,
      χ.changeLevel_primitiveCharacter,rfl⟩
  obtain ⟨j,hj,rfl⟩ := (Nat.dvd_prime_pow p.property).1 hd
  cases j with
  | zero =>
    exact (hn ((DirichletCharacter.eq_one_iff_conductor_eq_one χ).2 (by simpa using hc))).elim
  | succ j =>
    let k := e+1-(j+1)
    have hk : j+1+k=e+1 := by dsimp [k]; omega
    have hm : p.val^(e+1)=p.val^(j+1)*p.val^k := by rw [← pow_add,hk]
    refine ⟨j,k,hk,hc,?_⟩
    rw [← he,lifted_value p j k _ hm hd ψ hψ,GaussShell.norm_monomial p j k ψ hψ,
      mul_pow,Real.sq_sqrt (pow_nonneg (Nat.cast_nonneg _) _)]

theorem primitive_energy (p : Nat.Primes) (e : ℕ) (χ : DirichletCharacter ℂ (p.val^(e+1)))
    (hχ : χ.IsPrimitive) (z : ℂ) : ‖readout p (p.val^(e+1)) χ z‖^2=(p.val : ℝ)^(e+1) := by
  have he : p.val^(e+1)=p.val^(e+1)*p.val^0 := by simp
  have hv := lifted_value p e 0 _ he dvd_rfl χ hχ z
  rw [DirichletCharacter.changeLevel_self,pow_zero,mul_one] at hv
  rw [hv,RHTower.normSq_gaussSum_of_isPrimitive hχ,Nat.cast_pow]

theorem nonprincipal_imprimitive_energy (p : Nat.Primes) (e : ℕ)
    (χ : DirichletCharacter ℂ (p.val^(e+1))) (hn : χ≠1) (hi : ¬χ.IsPrimitive)
    {z : ℂ} (hz : ‖z‖≤1) :
    2*‖readout p (p.val^(e+1)) χ z‖^2 ≤ (p.val : ℝ)^(e+1) := by
  obtain ⟨j,k,he,hc,hval⟩ := nonprincipal_shape p e χ hn z
  have hk : k≠0 := by
    rintro rfl
    simp only [add_zero] at he
    exact hi (by rwa [DirichletCharacter.isPrimitive_def,hc,he])
  have hQ : 2≤p.val^k := by
    have := one_lt_pow₀ p.property.one_lt hk
    omega
  have hz₀ : (‖z‖^k)^2≤1 := pow_le_one₀ (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hz)
  rw [hval,← he,pow_add]
  have hP : 0≤(p.val : ℝ)^(j+1) := by positivity
  have h2 : (2 : ℝ)≤(p.val : ℝ)^k := by exact_mod_cast hQ
  calc
    _ ≤ 2*((p.val : ℝ)^(j+1)*1) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz₀ hP) (by norm_num)
    _ ≤ _ := by simpa only [mul_one,mul_comm] using mul_le_mul_of_nonneg_left h2 hP

private theorem principal_gap (p : Nat.Primes) (e : ℕ) {z : ℂ} (hz : ‖z‖≤1) :
    9*‖readout p (p.val^(e+1)) 1 z‖^2 ≤ 8*(p.val : ℝ)^(e+1) := by
  have h₁ : (1 : ℝ)<p.val := by exact_mod_cast p.property.one_lt
  have h₂ : (2 : ℝ)≤p.val := by exact_mod_cast p.property.two_le
  have hp := zero_lt_one.trans h₁
  rw [principal_value p e hz]
  have ht := PrincipalRamanujan.transfer_bound h₁ (r := 1) one_pos le_rfl e hz
  simp only [one_pow,one_mul] at ht
  have he : 9*(p.val*(1+1)/(p.val+1) : ℝ)^2 ≤ 8*p.val := by
    rw [div_pow,← mul_div_assoc,div_le_iff₀ (pow_pos (by positivity) 2)]
    nlinarith only [mul_nonneg hp.le (mul_nonneg (by linarith only [h₂] : 0≤2*(p.val : ℝ)-1)
      (sub_nonneg.mpr h₂))]
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 ht
  have hpow : (p.val : ℝ) ≤ (p.val : ℝ)^(e+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ h₁.le (by omega : 1≤e+1)
  linarith only [hh,he,hpow]

/-- Universal imprimitive gap, with equality possible at the dyadic principal
factor of modulus two. -/
theorem imprimitive_gap (p : Nat.Primes) (e : ℕ) (χ : DirichletCharacter ℂ (p.val^(e+1)))
    (hi : ¬χ.IsPrimitive) {z : ℂ} (hz : ‖z‖≤1) :
    9*‖readout p (p.val^(e+1)) χ z‖^2 ≤ 8*(p.val : ℝ)^(e+1) := by
  by_cases hn : χ=1
  · subst χ
    exact principal_gap p e hz
  · linarith only [nonprincipal_imprimitive_energy p e χ hn hi hz,
      sq_nonneg ‖readout p (p.val^(e+1)) χ z‖,(pow_nonneg (Nat.cast_nonneg p.val) (e+1) :
      0 ≤ (p.val : ℝ)^(e+1))]

/-- One strict numerical test identifies primitivity of the character at
every damping |z|≤1. -/
theorem primitive_iff_above_gap (p : Nat.Primes) (e : ℕ) (χ : DirichletCharacter ℂ (p.val^(e+1)))
    {z : ℂ} (hz : ‖z‖≤1) : χ.IsPrimitive ↔
      8*(p.val : ℝ)^(e+1)<9*‖readout p (p.val^(e+1)) χ z‖^2 := by
  constructor
  · intro h
    rw [primitive_energy p e χ h]
    have hp : 0<(p.val : ℝ)^(e+1) := pow_pos (Nat.cast_pos.mpr p.property.pos) _
    linarith only [hp]
  · intro h
    by_contra hi
    exact (not_lt_of_ge (imprimitive_gap p e χ hi hz)) h

/-- In the product of local Gauss transfers the same threshold detects
simultaneous primitivity. A single deficient component forces the full
product below the gap, independently of all the other phases. -/
theorem product_above_gap {ι : Type*} [Fintype ι] (p : ι → Nat.Primes) (e : ι → ℕ)
    (χ : ∀ i, DirichletCharacter ℂ ((p i).val^(e i+1))) (z : ι → ℂ) (hz : ∀ i, ‖z i‖≤1) :
    8*(∏ i, ((p i).val : ℝ)^(e i+1)) <
      9*‖∏ i, readout (p i) ((p i).val^(e i+1)) (χ i) (z i)‖^2 ↔
      ∀ i, (χ i).IsPrimitive := by
  classical
  let Q (i : ι) := ((p i).val : ℝ)^(e i+1)
  let T (i : ι) := ‖readout (p i) ((p i).val^(e i+1)) (χ i) (z i)‖^2
  have qpos (i : ι) : 0<Q i := pow_pos (Nat.cast_pos.mpr (p i).property.pos) _
  have tpos (i : ι) : 0≤T i := sq_nonneg _
  have primitive (i : ι) (h : (χ i).IsPrimitive) : T i=Q i :=
    primitive_energy _ _ _ h _
  have gap (i : ι) (h : ¬(χ i).IsPrimitive) : 9*T i≤8*Q i :=
    imprimitive_gap _ _ _ h (hz i)
  have dom (i : ι) : T i≤Q i := by
    by_cases hi : (χ i).IsPrimitive
    · exact (primitive i hi).le
    · linarith only [gap i hi,qpos i]
  rw [norm_prod,← Finset.prod_pow]
  change 8*(∏ i, Q i)<9*(∏ i, T i) ↔ _
  constructor
  · intro ht i
    by_contra hi
    have he := prod_le_prod (s := univ.erase i) (fun j _ => tpos j) (fun j _ => dom j)
    have h := mul_le_mul (gap i hi) he (prod_nonneg fun j _ => tpos j)
      (show 0≤8*Q i by have := qpos i; positivity)
    rw [← prod_erase_mul univ T (mem_univ i),← prod_erase_mul univ Q (mem_univ i)] at ht
    linarith only [ht,h]
  · intro hc
    rw [prod_congr rfl (fun i _ => primitive i (hc i))]
    have h := prod_pos (s := (univ : Finset ι)) (fun i _ => qpos i)
    linarith only [h]

/-- The principal character at level two attains the gap exactly at z=-1. -/
theorem dyadic_equality :
    9*‖readout ⟨2,Nat.prime_two⟩ 2 1 (-1)‖^2=8*(2 : ℝ) := by
  have h := principal_value ⟨2,Nat.prime_two⟩ 0 (z := -1) (by norm_num)
  change readout ⟨2,Nat.prime_two⟩ 2 1 (-1)=_ at h
  rw [h,PrincipalRamanujan.transfer]
  have ht := PrincipalRamanujan.fraction_at_edge (p := 2) (r := 1) (by norm_num) (by norm_num)
  norm_num at ht ⊢
  norm_num [ht]

end GaloisForLFunctions.PrimeExponentialSums.GaussGap

#print axioms GaloisForLFunctions.PrimeExponentialSums.GaussGap.principal_value
#print axioms GaloisForLFunctions.PrimeExponentialSums.GaussGap.nonprincipal_shape
#print axioms GaloisForLFunctions.PrimeExponentialSums.GaussGap.primitive_energy
#print axioms GaloisForLFunctions.PrimeExponentialSums.GaussGap.nonprincipal_imprimitive_energy
#print axioms GaloisForLFunctions.PrimeExponentialSums.GaussGap.imprimitive_gap
#print axioms GaloisForLFunctions.PrimeExponentialSums.GaussGap.primitive_iff_above_gap
#print axioms GaloisForLFunctions.PrimeExponentialSums.GaussGap.product_above_gap
#print axioms GaloisForLFunctions.PrimeExponentialSums.GaussGap.dyadic_equality
