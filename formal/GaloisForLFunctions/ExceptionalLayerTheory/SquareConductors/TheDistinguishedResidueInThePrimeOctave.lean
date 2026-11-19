import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCongruenceTermInTheReciprocalPrimePairSum
import GaloisForLFunctions.RHTower.Sieve.BuchstabIdentity

/-!
# The distinguished residue in an ordinary prime octave

Each prime imposes one forbidden residue. The average product of two
normalized sieve weights is the finite pair density from their common
primes. At the zero residue both the square-root sieve and the full
octave sieve select precisely the ordinary primes.
-/

noncomputable section
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Independent residues at the primes of one finite modulus. -/
abbrev PrimeResidues (S : Finset Nat.Primes) := (p : S) → Fin (p.val:ℕ)

local notation "finiteMean" => Finset.expect Finset.univ

private theorem mean_product {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i,Fintype (A i)] (f : ∀ i,A i → ℝ) :
    finiteMean (fun u : (i : ι) → A i => ∏ i,f i (u i))=∏ i,finiteMean (f i) := by
  classical
  simp only [Fintype.expect_eq_sum_div_card,←Fintype.prod_sum,Fintype.card_pi,Nat.cast_prod,prod_div_distrib]

private def forbiddenResidue (p : Nat.Primes) (d : ℕ) : Fin (p:ℕ) :=
  ⟨d%p,Nat.mod_lt _ p.prop.pos⟩

private def localSieveWeight (p : Nat.Primes) (d : ℕ) (t : Fin (p:ℕ)) : ℝ :=
  if t=forbiddenResidue p d then 0 else (p:ℝ)/((p:ℝ)-1)

private theorem mean_sieve_weight (p : Nat.Primes) (d : ℕ) : finiteMean (localSieveWeight p d)=1 := by
  let a := forbiddenResidue p d
  let c := (p:ℝ)/((p:ℝ)-1)
  have h (t : Fin (p:ℕ)) : localSieveWeight p d t=c-(if t=a then c else 0) := by
    dsimp only [a,c,localSieveWeight]; split_ifs <;> ring
  have hp : (1:ℝ) < p := by exact_mod_cast p.prop.one_lt
  simp only [Fintype.expect_eq_sum_div_card,h,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    sum_ite_eq',mem_univ,if_true]
  dsimp only [c]
  field_simp [show (p:ℝ)-1≠0 by linarith,show (p:ℝ)≠0 by linarith]
  ring

private theorem forbidden_residues_eq (p : Nat.Primes) (d h : ℕ) :
    forbiddenResidue p d=forbiddenResidue p (d+h) ↔ (p:ℕ) ∣ h := by
  change (⟨d%p,_⟩ : Fin (p:ℕ))=⟨(d+h)%p,_⟩ ↔ _
  rw [Fin.mk.injEq]
  change d ≡ d+h [MOD (p:ℕ)] ↔ _
  rw [Nat.modEq_iff_dvd' (Nat.le_add_right d h),Nat.add_sub_cancel_left]

private theorem mean_two_sieve_weights (p : Nat.Primes) (d h : ℕ) :
    finiteMean (fun t => localSieveWeight p d t * localSieveWeight p (d+h) t)=
      1+ramanujanLagWeight h p/((p:ℝ)-1)^2 := by
  let a := forbiddenResidue p d
  let b := forbiddenResidue p (d+h)
  let c := (p:ℝ)/((p:ℝ)-1)
  have hr (t : Fin (p:ℕ)) : localSieveWeight p d t*localSieveWeight p (d+h) t=
      c^2-(if t=a then c^2 else 0)-(if t=b then c^2 else 0)+
        (if t=a then (if a=b then c^2 else 0) else 0) := by
    change (if t=a then 0 else c)*(if t=b then 0 else c)=_
    by_cases ha : t=a
    · subst t; by_cases hb : a=b <;> simp only [hb,if_true,if_false,zero_mul] <;> ring
    · by_cases hb : t=b <;> simp only [ha,hb,if_true,if_false] <;> ring
  have hp : (1:ℝ) < p := by exact_mod_cast p.prop.one_lt
  simp only [Fintype.expect_eq_sum_div_card,hr,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,sum_ite_eq',mem_univ,if_true,BezoutValuationIncidence.ramanujanLagWeight_prime p.prop]
  have heq : a=b ↔ (p:ℕ) ∣ h := forbidden_residues_eq p d h
  simp only [heq]
  dsimp only [c]
  split_ifs <;> field_simp [show (p:ℝ)-1≠0 by linarith,show (p:ℝ)≠0 by linarith] <;> ring

private def activeFactor (p : Nat.Primes) (z d : ℕ) (t : Fin (p:ℕ)) :=
  if (p:ℕ) ≤ z then localSieveWeight p d t else 1

/-- The normalized weight left by the sieve truncated at z on a common residue space. -/
def residueSieveWeight (S : Finset Nat.Primes) (z d : ℕ) (t : PrimeResidues S) : ℝ :=
  ∏ p : S,activeFactor p.val z d (t p)

theorem residue_sieve_mean (S : Finset Nat.Primes) (z d : ℕ) :
    finiteMean (residueSieveWeight S z d)=1 := by
  classical
  rw [show residueSieveWeight S z d=(fun t : PrimeResidues S => ∏ p : S,activeFactor p.val z d (t p)) by rfl,
    mean_product]
  apply prod_eq_one
  intro p _
  by_cases hp : (p.val:ℕ) ≤ z
  · change finiteMean (fun t => if (p.val:ℕ) ≤ z then localSieveWeight p.val d t else 1)=1
    simp only [if_pos hp,mean_sieve_weight]
  · have hpos : (0:ℝ) < (p.val:ℕ) := Nat.cast_pos.mpr p.val.prop.pos
    simp [Fintype.expect_eq_sum_div_card,activeFactor,hp,hpos.ne']

/-- Only primes present at the left endpoint contribute to the joint density under nesting. -/
theorem residue_sieve_pair_mean (S : Finset Nat.Primes) {z w : ℕ} (hzw : z ≤ w) (d h : ℕ) :
    finiteMean (fun t : PrimeResidues S => residueSieveWeight S z d t * residueSieveWeight S w (d+h) t)=
      finitePairDensity (S.filter (fun p => (p:ℕ) ≤ z)) h := by
  classical
  simp only [residueSieveWeight,←prod_mul_distrib,mean_product]
  unfold finitePairDensity
  rw [prod_filter]
  change _ = ∏ p ∈ S,(if (p:ℕ) ≤ z then 1+ramanujanLagWeight h p/((p:ℝ)-1)^2 else 1)
  rw [←Finset.prod_attach]
  apply prod_congr rfl
  intro p _
  by_cases hz : (p.val:ℕ) ≤ z
  · simp only [activeFactor,if_pos hz,if_pos (hz.trans hzw),mean_two_sieve_weights]
  · by_cases hw : (p.val:ℕ) ≤ w
    · simp only [activeFactor,if_neg hz,if_pos hw,one_mul,mean_sieve_weight]
    · have hpos : (0:ℝ) < (p.val:ℕ) := Nat.cast_pos.mpr p.val.prop.pos
      simp [activeFactor,hz,hw,Fintype.expect_eq_sum_div_card,hpos.ne']

/-- The primes at which translations of the complete octave are tested. -/
def octaveSievePrimes (M : ℕ) : Finset Nat.Primes := (range (M+1)).subtype Nat.Prime

private theorem mem_octave_sieve_primes {M : ℕ} {p : Nat.Primes} :
    p∈octaveSievePrimes M ↔ (p:ℕ) ≤ M := by simp [octaveSievePrimes,Nat.lt_succ_iff]

/-- The product of the normalizing factors at active primes. -/
def sieveNormalization (S : Finset Nat.Primes) (z : ℕ) : ℝ :=
  ∏ p : S, if (p.val:ℕ) ≤ z then (p.val:ℝ)/((p.val:ℝ)-1) else 1

/-- The residue vector of the integer zero. -/
def zeroResidues (S : Finset Nat.Primes) : PrimeResidues S :=
  fun p => ⟨0,p.val.prop.pos⟩

private theorem origin_residue_iff (S : Finset Nat.Primes) (p : S) (d : ℕ) :
    zeroResidues S p=forbiddenResidue p.val d ↔ (p.val:ℕ) ∣ d := by
  rw [Nat.dvd_iff_mod_eq_zero]
  change (⟨0,_⟩ : Fin (p.val:ℕ))=⟨d%p.val,_⟩ ↔ _
  rw [Fin.mk.injEq,eq_comm]

/-- Every active prime test agrees with primality at the distinguished
residue once the cutoff reaches the square root and stays below d. -/
theorem square_root_sieve_at_zero {M z d : ℕ} (hM : 1 ≤ M) (hd : d∈Ioc M (2*M))
    (hz : (2*M).sqrt ≤ z) (hzM : z ≤ M) :
    residueSieveWeight (octaveSievePrimes M) z d (zeroResidues _) =
      if d.Prime then sieveNormalization (octaveSievePrimes M) z else 0 := by
  classical
  obtain ⟨hl,hh⟩ := mem_Ioc.mp hd
  by_cases hpr : d.Prime
  · rw [if_pos hpr]
    apply prod_congr rfl
    intro p _
    by_cases hpz : (p.val:ℕ) ≤ z
    · have hp : (p.val:ℕ) < d := (hpz.trans hzM).trans_lt hl
      have hind : ¬(p.val:ℕ) ∣ d := fun e => hp.ne ((Nat.prime_dvd_prime_iff_eq p.val.prop hpr).mp e)
      simp only [activeFactor,hpz,if_true,localSieveWeight,origin_residue_iff,if_neg hind]
    · simp only [activeFactor,if_neg hpz]
  · rw [if_neg hpr]
    let p : Nat.Primes := ⟨d.minFac,Nat.minFac_prime (by omega)⟩
    have hpz : (p:ℕ) ≤ z := (Nat.le_sqrt.mpr (by
      simpa only [←pow_two] using (Nat.minFac_sq_le_self (by omega : 0 < d) hpr).trans hh)).trans hz
    let j : octaveSievePrimes M := ⟨p,mem_octave_sieve_primes.mpr (hpz.trans hzM)⟩
    apply prod_eq_zero (mem_univ j)
    have hdiv : (j.val:ℕ) ∣ d := Nat.minFac_dvd d
    simp only [activeFactor,show (j.val:ℕ) ≤ z from hpz,if_true,localSieveWeight,origin_residue_iff,if_pos hdiv]

/-- Both exact sieves recover the ordinary prime logarithm by affine
interpolation at zero, with the normalization difference cleared. -/
theorem calibrated_prime_at_zero {M d : ℕ} (hM : 2 ≤ M) (hd : d∈Ioc M (2*M)) :
    let S := octaveSievePrimes M
    let z := (2*M).sqrt
    let A := sieveNormalization S z
    let B := sieveNormalization S M
    (B-Real.log d)*(residueSieveWeight S z d (zeroResidues S)-1)+
      (Real.log d-A)*(residueSieveWeight S M d (zeroResidues S)-1)=
      (B-A)*((if d.Prime then Real.log d else 0)-1) := by
  have hm : (2*M).sqrt ≤ M := Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr (by nlinarith only [Nat.zero_le (M^2)]))
  dsimp only
  rw [square_root_sieve_at_zero (by omega) hd le_rfl hm,square_root_sieve_at_zero (by omega) hd hm le_rfl]
  split_ifs <;> ring

#print axioms residue_sieve_pair_mean
#print axioms square_root_sieve_at_zero
#print axioms calibrated_prime_at_zero

private theorem residues_nonempty (S : Finset Nat.Primes) : Nonempty (PrimeResidues S) :=
  ⟨zeroResidues S⟩

private theorem centered_sieve_pair_mean (S : Finset Nat.Primes) {z w : ℕ} (hzw : z ≤ w) (d h : ℕ) :
    finiteMean (fun t : PrimeResidues S =>
      (residueSieveWeight S z d t-1)*(residueSieveWeight S w (d+h) t-1))=
        finitePairDensity (S.filter (fun p => (p:ℕ) ≤ z)) h-1 := by
  let f := residueSieveWeight S z d
  let g := residueSieveWeight S w (d+h)
  have hr (t : PrimeResidues S) : (f t-1)*(g t-1)=(f t*g t-f t)-(g t-1) := by ring
  haveI := residues_nonempty S
  have h1 : finiteMean (fun _ : PrimeResidues S => (1:ℝ))=1 := by
    simp [Fintype.expect_eq_sum_div_card,Fintype.card_ne_zero]
  change finiteMean (fun t => (f t-1)*(g t-1))=_
  simp only [hr,expect_sub_distrib,h1]
  rw [show finiteMean f=1 from residue_sieve_mean ..,show finiteMean g=1 from residue_sieve_mean ..,
    residue_sieve_pair_mean S hzw d h]
  ring

private theorem zero_gap_density (S : Finset Nat.Primes) (z : ℕ) :
    finitePairDensity (S.filter (fun p => (p:ℕ) ≤ z)) 0=sieveNormalization S z := by
  classical
  rw [finitePairDensity,prod_filter,←prod_attach]
  apply prod_congr rfl
  intro p _
  by_cases hp : (p.val:ℕ) ≤ z
  · have hp1 : (1:ℝ) < p.val := by exact_mod_cast p.val.prop.one_lt
    simp only [if_pos hp,BezoutValuationIncidence.ramanujanLagWeight_prime p.val.prop,dvd_zero,if_true]
    field_simp [show (p.val:ℝ)-1≠0 by linarith]; ring
  · simp only [if_neg hp]

/-- Total reciprocal centered sieve weight on the exact interval. -/
def reciprocalResidueSum (S : Finset Nat.Primes) (z : ℕ → ℕ) (L H : ℕ) (t : PrimeResidues S) : ℝ :=
  ∑ d ∈ Ioc L H,(d:ℝ)⁻¹*(residueSieveWeight S (z d) d t-1)

private theorem offset_Ioc (L H : ℕ) (f : ℕ → ℝ) :
    (∑ e ∈ Ioc L H,f e)=∑ h ∈ Icc 1 (H-L), f (L+h) := by
  rw [show Icc 1 (H-L)=Ioc 0 (H-L) by ext h; simp only [mem_Icc,mem_Ioc]; omega]
  apply sum_nbij' (fun e => e-L) (fun h => L+h)
  · intro e he; simp only [mem_Ioc] at he ⊢; omega
  · intro h hh; simp only [mem_Ioc] at hh ⊢; omega
  · intro e he; have := (mem_Ioc.mp he).1; omega
  · intro h _; omega
  · intro e he; have := (mem_Ioc.mp he).1; rw [show L+(e-L)=e by omega]

/-- In a nested sieve the covariance of one entry with all its later
partners has nonpositive reciprocal mean. -/
private theorem left_residue_covariance (S : Finset Nat.Primes) {z : ℕ → ℕ} (hz : Monotone z)
    {d : ℕ} (hd : 0 < d) (H : ℕ) :
    finiteMean (fun t : PrimeResidues S => (residueSieveWeight S (z d) d t-1)*
      reciprocalResidueSum S z d H t) ≤ 0 := by
  let f (j : ℕ) (t : PrimeResidues S) := residueSieveWeight S (z j) j t-1
  have hr (t : PrimeResidues S) :
      f d t*reciprocalResidueSum S z d H t =
        ∑ h ∈ Icc 1 (H-d),((d:ℝ)+h)⁻¹*(f d t*f (d+h) t) := by
    dsimp only [reciprocalResidueSum]
    rw [offset_Ioc,mul_sum]
    apply sum_congr rfl
    intro i _
    dsimp only [f]; rw [Nat.cast_add]; ring
  change finiteMean (fun t => f d t*reciprocalResidueSum S z d H t) ≤ 0
  simp only [hr,expect_sum_comm,←mul_expect,f,centered_sieve_pair_mean S (hz (Nat.le_add_right _ _))]
  have h := finite_weighted_pair_density_le (S.filter (fun p => (p:ℕ) ≤ z d)) (H-d)
    (fun i : ℕ => ((d:ℝ)+i)⁻¹)
    (fun i j hij => inv_anti₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hij)))
    (fun i => by positivity)
  simpa only [mul_comm] using h

private theorem interval_insert_left (L H : ℕ) (hh : L < H) :
    Ioc L H=insert (L+1) (Ioc (L+1) H) := by
  ext i
  simp only [mem_Ioc,mem_insert]
  omega

/-- The sum of the individual diagonal variances bounds the entire
reciprocal interval at all sieve cutoffs increasing with the integer. -/
theorem reciprocal_residue_mean_square (S : Finset Nat.Primes) {z : ℕ → ℕ} (hz : Monotone z)
    (L H : ℕ) :
    finiteMean (fun t => (reciprocalResidueSum S z L H t)^2) ≤
      ∑ d ∈ Ioc L H,(d:ℝ)⁻¹^2*(sieveNormalization S (z d)-1) := by
  generalize he : H-L=j
  induction j generalizing L with
  | zero =>
    have hl : H ≤ L := by omega
    simp [reciprocalResidueSum,Ioc_eq_empty_of_le hl]
  | succ j ih =>
    have hl : L < H := by omega
    let d := L+1
    let f (t : PrimeResidues S) := residueSieveWeight S (z d) d t-1
    let g := reciprocalResidueSum S z d H
    have hd : 0 < d := Nat.succ_pos _
    have hnot : d∉Ioc d H := by simp
    have hsplit : Ioc L H=insert d (Ioc d H) := interval_insert_left L H hl
    have hr (t : PrimeResidues S) : (reciprocalResidueSum S z L H t)^2=
        (d:ℝ)⁻¹^2*(f t*f t)+(2*(d:ℝ)⁻¹)*(f t*g t)+(g t)^2 := by
      rw [reciprocalResidueSum,hsplit,sum_insert hnot]
      change ((d:ℝ)⁻¹*f t+g t)^2=_
      ring
    have hdiag : finiteMean (fun t => f t*f t)=sieveNormalization S (z d)-1 := by
      simpa only [f,Nat.add_zero,zero_gap_density] using
        centered_sieve_pair_mean S (z := z d) le_rfl d 0
    have hcross := left_residue_covariance S hz hd H
    have hj := ih (L := d) (by dsimp only [d]; omega)
    simp only [hr,expect_add_distrib,←mul_expect,hdiag,hsplit,sum_insert hnot]
    exact (add_le_add (add_le_of_nonpos_right
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hcross)) le_rfl).trans (add_le_add le_rfl hj)

#print axioms reciprocal_residue_mean_square

/-- Convex combinations of nested finite sieves preserve the reciprocal
mean-square bound, even when the chosen cutoff differs at every endpoint. -/
theorem reciprocal_residue_mixture_square {ι : Type*} (S : Finset Nat.Primes) (J : Finset ι)
    (a : ι → ℝ) (ha : ∀ j ∈ J,0 ≤ a j) (hmass : ∑ j ∈ J,a j=1)
    (z : ι → ℕ → ℕ) (hz : ∀ j ∈ J,Monotone (z j)) (L H : ℕ) :
    finiteMean (fun t => (∑ j ∈ J,a j*reciprocalResidueSum S (z j) L H t)^2) ≤
      ∑ d ∈ Ioc L H,(d:ℝ)⁻¹^2*((∑ j ∈ J,a j*sieveNormalization S (z j d))-1) := by
  let f (j : ι) := reciprocalResidueSum S (z j) L H
  have hrow (t : PrimeResidues S) :
      (∑ j ∈ J,a j*f j t)^2 ≤ ∑ j ∈ J,a j*(f j t)^2 := by
    let c := ∑ j ∈ J,a j*f j t
    have hvar := sum_nonneg (s := J) (fun j hj => mul_nonneg (ha j hj) (sq_nonneg (f j t-c)))
    have h (j : ι) : a j*(f j t-c)^2=a j*(f j t)^2-(a j*f j t)*(2*c)+a j*c^2 := by ring
    simp_rw [h] at hvar
    rw [sum_add_distrib,sum_sub_distrib,←sum_mul,←sum_mul,hmass,one_mul] at hvar
    change 0 ≤ (∑ j ∈ J,a j*(f j t)^2)-c*(2*c)+c^2 at hvar
    change c^2 ≤ _
    linarith only [hvar]
  have hm := expect_le_expect (s := (univ : Finset (PrimeResidues S))) (fun t _ => hrow t)
  rw [expect_sum_comm] at hm
  simp only [←mul_expect] at hm
  have ub := sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left
    (reciprocal_residue_mean_square S (hz j hj) L H) (ha j hj))
  apply (hm.trans ub).trans_eq
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [show (∑ j ∈ J,a j*sieveNormalization S (z j d))-1=
    ∑ j ∈ J,a j*(sieveNormalization S (z j d)-1) by
    simp only [mul_sub,mul_one,sum_sub_distrib,hmass],mul_sum]
  exact sum_congr rfl fun j _ => by ring

#print axioms reciprocal_residue_mixture_square

/-- Proportion of residues where the two normalized survivor masses agree,
multiplied by the squared difference forced there. -/
theorem square_root_sieve_agreement_density (S : Finset Nat.Primes) (z w L H : ℕ) :
    let A := sieveNormalization S z
    let B := sieveNormalization S w
    let U := reciprocalResidueSum S (fun _ => z) L H
    let V := reciprocalResidueSum S (fun _ => w) L H
    let J := ∑ d ∈ Ioc L H,(d:ℝ)⁻¹^2
    let T := ∑ d ∈ Ioc L H,(d:ℝ)⁻¹
    finiteMean (fun t => if B*(U t+T)=A*(V t+T) then ((A-B)*T)^2 else 0) ≤
      2*J*(B^2*(A-1)+A^2*(B-1)) := by
  classical
  let A := sieveNormalization S z
  let B := sieveNormalization S w
  let U := reciprocalResidueSum S (fun _ => z) L H
  let V := reciprocalResidueSum S (fun _ => w) L H
  let J := ∑ d ∈ Ioc L H,(d:ℝ)⁻¹^2
  let T := ∑ d ∈ Ioc L H,(d:ℝ)⁻¹
  have row (t : PrimeResidues S) :
      (if B*(U t+T)=A*(V t+T) then ((A-B)*T)^2 else 0) ≤
        (2*B^2)*(U t)^2+(2*A^2)*(V t)^2 := by
    split_ifs with h
    · have he : (A-B)*T=B*U t-A*V t := by linear_combination -h
      rw [he]
      nlinarith only [sq_nonneg (B*U t+A*V t)]
    · positivity
  have hm := expect_le_expect (s := (univ : Finset (PrimeResidues S))) (fun t _ => row t)
  rw [expect_add_distrib,←mul_expect,←mul_expect] at hm
  have hu := reciprocal_residue_mean_square S (z := fun _ => z) monotone_const L H
  have hv := reciprocal_residue_mean_square S (z := fun _ => w) monotone_const L H
  rw [←sum_mul] at hu hv
  change _ ≤ 2*J*(B^2*(A-1)+A^2*(B-1))
  exact hm.trans ((add_le_add (mul_le_mul_of_nonneg_left hu (by positivity))
    (mul_le_mul_of_nonneg_left hv (by positivity))).trans_eq (by ring))

/-- Ordinary factorization forces agreement of the two survivor masses
at residue zero through the full terminal. -/
theorem square_root_sieve_agreement_at_zero {M : ℕ} (hM : 2 ≤ M) :
    let S := octaveSievePrimes M
    let z := (2*M).sqrt
    let T := ∑ d ∈ Ioc M (2*M),(d:ℝ)⁻¹
    sieveNormalization S M*(reciprocalResidueSum S (fun _ => z) M (2*M) (zeroResidues S)+T)=
      sieveNormalization S z*(reciprocalResidueSum S (fun _ => M) M (2*M) (zeroResidues S)+T) := by
  let S := octaveSievePrimes M
  let z := (2*M).sqrt
  let T := ∑ d ∈ Ioc M (2*M),(d:ℝ)⁻¹
  have hz : z ≤ M := Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr (by nlinarith only [Nat.zero_le (M^2)]))
  have hs (w : ℕ) (hw : z ≤ w) (hwM : w ≤ M) :
      reciprocalResidueSum S (fun _ => w) M (2*M) (zeroResidues S)+T =
        sieveNormalization S w*∑ d ∈ Ioc M (2*M),if d.Prime then (d:ℝ)⁻¹ else 0 := by
    dsimp only [reciprocalResidueSum,T]
    rw [←sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro d hd
    rw [square_root_sieve_at_zero (by omega) hd hw hwM]
    split_ifs <;> ring
  change sieveNormalization S M*(_+T)=sieveNormalization S z*(_+T)
  rw [hs z le_rfl hz,hs M hz le_rfl]
  ring

#print axioms square_root_sieve_agreement_density
#print axioms square_root_sieve_agreement_at_zero

open _root_.RHTower.Sieve in
/-- The gap between the two sifting levels on a positive translate
consists exactly of the ordered semiprimes beyond the old right endpoint.
The Buchstab sum counts a square once. -/
theorem translated_sieve_boundary {M t d : ℕ} (hM : 5 ≤ M) (ht : t ≤ M)
    (hd : d∈Ioc M (2*M)) :
    let n := d+t
    let y := (2*M).sqrt+1
    rho n (M+1) + (∑ p ∈ (Ico y (M+1)).filter (fun p => p.Prime ∧ p ∣ n),
      if 2*M < n ∧ p ≤ n/p ∧ (n/p).Prime then 1 else 0)=rho n y := by
  let y := (2*M).sqrt+1
  let n := d+t
  obtain ⟨hdlo,hdhi⟩ := mem_Ioc.mp hd
  have hn : M < n := by dsimp only [n]; omega
  have hn3 : n ≤ 3*M := by dsimp only [n]; omega
  have hy3 : 3 ≤ y := by
    have hl := Nat.le_sqrt'.mpr (by omega : 2^2 ≤ 2*M)
    dsimp only [y]; omega
  have hy2 : 2*M < y^2 := Nat.lt_succ_sqrt' _
  have hyM : y ≤ M+1 := Nat.succ_le_succ (Nat.le_of_lt_succ
    (Nat.sqrt_lt'.mpr (by nlinarith only [Nat.zero_le (M^2)])))
  have hN : 0 < n := by omega
  change rho n (M+1)+_=rho n y
  rw [←buchstab hN hyM]
  congr 1
  apply sum_congr rfl
  intro p hp
  obtain ⟨hi,hpr,hdv⟩ := mem_filter.mp hp
  obtain ⟨hyp,hpm⟩ := mem_Ico.mp hi
  let q := n/p
  have hpq : p*q=n := Nat.mul_div_cancel' hdv
  have hq1 : 1 < q := by
    by_contra! hh
    have hu := Nat.mul_le_mul_left p hh
    rw [hpq,Nat.mul_one] at hu
    omega
  have hqM : q ≤ M := by
    have hh := (Nat.mul_le_mul_right q (hy3.trans hyp)).trans_eq hpq
    omega
  have hqsmall : q < p^2 := by
    have hpp := Nat.pow_le_pow_left hyp 2
    omega
  change (if 2*M < n ∧ p ≤ q ∧ q.Prime then 1 else 0)=rho q p
  by_cases hρ : rho q p=1
  · have hall := (rho_eq_one_iff.mp hρ).2
    have hmin := Nat.minFac_prime (by omega : q≠1)
    have hl := hall q.minFac (Nat.mem_primeFactors.mpr ⟨hmin,Nat.minFac_dvd _,by omega⟩)
    have hqp : q.Prime := by
      by_contra h
      exact (not_le_of_gt hqsmall) ((Nat.pow_le_pow_left hl 2).trans (Nat.minFac_sq_le_self (by omega) h))
    have horder := hall q (Nat.mem_primeFactors.mpr ⟨hqp,dvd_rfl,by omega⟩)
    have hupper : 2*M < n := hy2.trans_le (by
      rw [←hpq,pow_two]
      exact Nat.mul_le_mul hyp (hyp.trans horder))
    rw [if_pos ⟨hupper,horder,hqp⟩,hρ]
  · have hzero : rho q p=0 := by have hh := rho_le_one q p; omega
    have hno : ¬(2*M < n ∧ p ≤ q ∧ q.Prime) := by
      rintro ⟨_,hpq',hqp⟩
      apply hρ
      exact rho_eq_one_iff.mpr ⟨hqp.pos,fun k hk => by
        have heq := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hk) hqp).mp (Nat.dvd_of_mem_primeFactors hk)
        exact heq ▸ hpq'⟩
    rw [if_neg hno,hzero]

#print axioms translated_sieve_boundary

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
