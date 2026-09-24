import GaloisForLFunctions.RHTower.MobiusDivisorTwoChannelPrimeBlocks
import GaloisForLFunctions.RHTower.MobiusDivisorSmallCoreInteractions

/-!
# Arbitrary-core mixed sign in the first two quotient channels

The actual source's first two defects are nonnegative. Concavity of the
square-root block increments then shows that, below the third quotient
threshold, the two-cofactor channel cannot exceed the one-cofactor channel.
Every prime partner above one-third of the cutoff therefore retains its
original orientation, regardless of how many older primes were processed.
Two such partners have nonnegative mixed energy curvature. This removes
their mutual pair interaction as a source of negative CCM-FU compensation;
it does not control interactions with smaller primes or any global schedule.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

private theorem first_two_defect_nonneg :
    0 ≤ primeFreeDivisorDefect 1 ∧ 0 ≤ primeFreeDivisorDefect 2 := by
  have h := (harmonic_mascheroni_half_bounds (n := 16) (by norm_num)).2
  have hlog : Real.log (16:ℝ)=4*Real.log 2 := by
    rw [show (16:ℝ)=2^(4 : ℕ) by norm_num,Real.log_pow]
    norm_num
  norm_num [harmonic,Finset.sum_range_succ,hlog] at h
  have hg : (5768/10000:ℝ) ≤ Real.eulerMascheroniConstant := by
    linarith [Real.log_two_lt_d9]
  constructor <;> norm_num [primeFreeDivisorDefect,Finset.sum_Icc_succ_top] <;>
    linarith [Real.log_two_gt_d9]

/-- Concavity of the first two square-root blocks makes the two-cofactor
    expenditure no greater than the unit-cofactor expenditure. -/
theorem divisorUnsignedDilationChannel_double_le_of_le_three_mul
    {M p : ℕ} (hp : 0<p) (hMp : M≤3*p) :
    divisorUnsignedDilationChannel M (2*p) ≤ divisorUnsignedDilationChannel M p := by
  by_cases hlo : M≤2*p
  · have hz : divisorUnsignedDilationChannel M (2*p)=0 := by
      simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<2*p)]
    rw [hz]
    exact divisorUnsignedDilationChannel_nonneg M p
  have h2 : 2*p<M := by omega
  have hsecond : divisorUnsignedDilationChannel M p =
      Real.sqrt p*(Real.sqrt 2-1)*primeFreeDivisorDefect 1+
        (Real.sqrt M-Real.sqrt (2*p:ℕ))*primeFreeDivisorDefect 2 := by
    have hh := divisorUnsignedDilationChannel_mul_add p 2 (M-2*p) 1 hp (by omega)
    have hM : p*2+(M-2*p)=M := by omega
    have hK : divisorUnsignedDilationChannel 2 1=
        (Real.sqrt 2-1)*primeFreeDivisorDefect 1 := by
      simpa using (divisorUnsignedDilationChannel_eq_first_block (M := 2) (d := 1)
        (by omega) (by omega) (by omega))
    rw [hM] at hh
    simpa only [Nat.mul_one,hK,Nat.mul_comm p 2,Nat.div_one,mul_assoc] using hh
  have hfirst : divisorUnsignedDilationChannel M (2*p)=
      (Real.sqrt M-Real.sqrt (2*p:ℕ))*primeFreeDivisorDefect 1 := by
    simpa using (divisorUnsignedDilationChannel_eq_first_block
      (M := M) (d := 2*p) (by omega) h2 (by omega))
  rw [hfirst,hsecond]
  have hs2lo : (7/5:ℝ)≤Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hs3hi : Real.sqrt 3≤(9/5:ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hrootM : Real.sqrt M≤Real.sqrt 3*Real.sqrt p := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤3)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hMp)
  have hroot2 : Real.sqrt (2*p:ℕ)=Real.sqrt 2*Real.sqrt p := by
    rw [Nat.cast_mul,Real.sqrt_mul (by norm_num)]
    norm_num
  have hgap : Real.sqrt M-Real.sqrt (2*p:ℕ) ≤ Real.sqrt p*(Real.sqrt 2-1) := by
    rw [hroot2]
    have hscale2 := mul_le_mul_of_nonneg_right hs2lo (Real.sqrt_nonneg (p:ℝ))
    have hscale3 := mul_le_mul_of_nonneg_right hs3hi (Real.sqrt_nonneg (p:ℝ))
    nlinarith only [hrootM,hscale2,hscale3]
  have hposgap : 0≤Real.sqrt M-Real.sqrt (2*p:ℕ) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast h2.le))
  have hD := first_two_defect_nonneg
  have hmain := mul_le_mul_of_nonneg_right hgap hD.1
  have htail := mul_nonneg hposgap hD.2
  nlinarith only [hmain,htail]

private theorem divisorUnsignedDilationChannel_double_le_low_cutoff
    (N d : ℕ) (hN : N≤3) :
    divisorUnsignedDilationChannel N (2*d) ≤ divisorUnsignedDilationChannel N d := by
  by_cases hd0 : d=0
  · subst d
    simp [divisorUnsignedDilationChannel,primeFreeDivisorDefect]
  by_cases hd1 : d=1
  · subst d
    simpa using divisorUnsignedDilationChannel_double_le_of_le_three_mul
      (M := N) (p := 1) (by omega) (by omega)
  have hd2 : 2≤d := by omega
  have hNd : N≤2*d := by omega
  have hz : divisorUnsignedDilationChannel N (2*d)=0 := by
    simp [divisorUnsignedDilationChannel,Icc_eq_empty_of_lt (by omega : N-1<2*d)]
  rw [hz]
  exact divisorUnsignedDilationChannel_nonneg N d

private theorem low_cutoff_oriented_nonneg
    (N : ℕ) (P R : Finset ℕ) (hN : N≤3)
    (hP : P⊆{2}) (hR : ∀ r∈R,r.Prime) :
    0 ≤ mobiusDivisorOrientedFibre N P R := by
  by_cases h2P : 2∈P
  · have hPeq : P={2} := by
      apply Subset.antisymm hP
      simpa using singleton_subset_iff.mpr h2P
    subst P
    by_cases h2R : 2∈R
    · unfold mobiusDivisorOrientedFibre
      rw [show ({2}:Finset ℕ)=insert 2 ∅ by rfl,
        mobiusDivisorSelectionFibre_insert,if_pos h2R]
      simp
    · have he := mobiusDivisorOrientedFibre_sparse_prime_block N {2} R
        (by
          intro p hp
          have he : p=2 := Finset.mem_singleton.mp hp
          exact he.symm ▸ Nat.prime_two)
        (by intro p hp q hq hpq; simp at hp hq; omega)
        hR (disjoint_singleton_right.mpr h2R)
      rw [he]
      simpa only [sum_singleton] using
        (show 0 ≤ divisorUnsignedDilationChannel N (∏ r∈R,r)-
          divisorUnsignedDilationChannel N (2*∏ r∈R,r) from
          sub_nonneg.mpr (divisorUnsignedDilationChannel_double_le_low_cutoff
            N (∏ r∈R,r) hN))
  · have hPeq : P=∅ := by
      ext r
      constructor
      · intro hr
        have hr2 : r=2 := by simpa using hP hr
        exact False.elim (h2P (hr2 ▸ hr))
      · simp
    subst P
    rw [mobiusDivisorOrientedFibre_empty_eq_unsigned_product R hR N]
    exact divisorUnsignedDilationChannel_nonneg N _

/-- Every upper-third fresh prime partner retains the original Möbius
orientation in each residual prime coordinate after any processed core. -/
theorem third_sector_partner_oriented_nonpos
    (M : ℕ) (P R : Finset ℕ) (hP : ∀ r∈P,r.Prime)
    (hR : ∀ r∈R,r.Prime) {p : ℕ} (hp : p.Prime)
    (hpP : p∉P) (hpR : p∉R) (hMp : M<3*p) :
    (-1:ℝ)^R.card*mobiusDivisorSelectionFibre M P (insert p R) ≤ 0 := by
  let Q := P.filter (fun r => r<3)
  have hQ : Q⊆{2} := by
    intro r hr
    obtain ⟨hrP,hr3⟩ := Finset.mem_filter.mp hr
    have hr2 := (hP r hrP).two_le
    have he : r=2 := by omega
    simp [he]
  have hpQ : p∉Q := fun h => hpP (Finset.mem_filter.mp h).1
  have hcut : M/p+1≤3 := by
    have h := (Nat.div_lt_iff_lt_mul hp.pos).mpr hMp
    omega
  have hA : 0≤(-1:ℝ)^R.card*mobiusDivisorSelectionFibre (M/p) Q R := by
    simpa only [mobiusDivisorOrientedFibre] using
      low_cutoff_oriented_nonneg (M/p) Q R (by omega) hQ hR
  have hB : 0≤(-1:ℝ)^R.card*mobiusDivisorSelectionFibre (M/p+1) Q R := by
    simpa only [mobiusDivisorOrientedFibre] using
      low_cutoff_oriented_nonneg (M/p+1) Q R hcut hQ hR
  have hw0 := divisorPrimeClipWeight_nonneg M p hp.pos
  have hw1 : 0≤1-divisorPrimeClipWeight M p := by
    have h := divisorPrimeClipWeight_lt_one M p hp.pos
    linarith only [h]
  have hinterp : 0≤(-1:ℝ)^R.card*mobiusDivisorInterpolatedFibre M p Q R := by
    unfold mobiusDivisorInterpolatedFibre
    have h0 := mul_nonneg hw1 hA
    have h1 := mul_nonneg hw0 hB
    nlinarith only [h0,h1]
  rw [mobiusDivisorSelectionFibre_partner_filter_cutoff M 3 P R hp hpP hpR hcut,
    mobiusDivisorSelectionFibre_prime_interpolation hp M Q R hpQ hpR]
  have hm := mul_nonneg (Real.sqrt_nonneg (p:ℝ)) hinterp
  nlinarith only [hm]

/-- All pairwise mixed energy curvature of distinct primes above one-third
    cutoff is nonnegative, even after an arbitrary old processed prime core. -/
theorem mobiusDivisorSelectionEnergy_mixed_nonneg_third_sector
    (M : ℕ) (P : Finset ℕ) (hM : 9≤M) (hP : ∀ r∈P,r.Prime)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpM : p<M) (hqM : q<M) (hpP : p∉P) (hqP : q∉P)
    (hpq : p≠q) (hMp : M<3*p) (hMq : M<3*q) :
    0 ≤ mobiusDivisorSelectionEnergy M (insert q (insert p P))-
      mobiusDivisorSelectionEnergy M (insert p P)-
      mobiusDivisorSelectionEnergy M (insert q P)+mobiusDivisorSelectionEnergy M P := by
  have hprod : M≤p*q := by
    have hq3 : 3≤q := by omega
    have hmul := Nat.mul_le_mul_left p hq3
    nlinarith only [hMp,hmul]
  rw [mobiusDivisorSelectionEnergy_mixed_eq M P hp hq hpM hqM hpP hqP hpq]
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro R hR
  have hpR : p∉R := fun h => (Finset.mem_erase.mp (Finset.mem_powerset.mp hR h)).1 rfl
  have hqR : q∉R := fun h =>
    (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_powerset.mp hR h)).2).1 rfl
  have hprime : ∀ r∈R,r.Prime := by
    intro r hr
    exact (Finset.mem_filter.mp
      (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_powerset.mp hR hr)).2).2).2
  have hz : mobiusDivisorSelectionFibre M P (insert p (insert q R))=0 := by
    apply mobiusDivisorSelectionFibre_eq_zero_of_le_product
    rw [Finset.prod_insert (by simp [hpq,hpR]),Finset.prod_insert hqR]
    have hRpos : 1≤∏ r∈R,r := Finset.prod_pos (fun r hr => (hprime r hr).pos)
    calc
      M ≤ p*q := hprod
      _ = (p*q)*1 := by ring
      _ ≤ (p*q)*(∏ r∈R,r) := Nat.mul_le_mul_left _ hRpos
      _ = _ := by ring
  rw [hz,mul_zero,zero_add]
  let s : ℝ := (-1)^R.card
  have hs : s*s=1 := by
    dsimp [s]
    rw [← pow_add,show R.card+R.card=2*R.card by omega,pow_mul]
    norm_num
  have hpn := third_sector_partner_oriented_nonpos M P R hP hprime hp hpP hpR hMp
  have hqn := third_sector_partner_oriented_nonpos M P R hP hprime hq hqP hqR hMq
  have hsign := mul_nonneg_of_nonpos_of_nonpos hpn hqn
  have he : (s*mobiusDivisorSelectionFibre M P (insert p R))*
      (s*mobiusDivisorSelectionFibre M P (insert q R)) =
      mobiusDivisorSelectionFibre M P (insert p R)*
      mobiusDivisorSelectionFibre M P (insert q R) := by
    calc
      _ = (s*s)*(mobiusDivisorSelectionFibre M P (insert p R)*
          mobiusDivisorSelectionFibre M P (insert q R)) := by ring
      _ = _ := by rw [hs,one_mul]
  exact he ▸ hsign

end RHTower
