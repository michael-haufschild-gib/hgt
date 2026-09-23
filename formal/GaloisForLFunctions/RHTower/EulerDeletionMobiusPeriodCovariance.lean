import GaloisForLFunctions.RHTower.EulerDeletionCoprimeWordPeriodicity
import GaloisForLFunctions.RHTower.EulerDeletionMobiusGlobalLogSaving

/-!
# Complete-period covariance of literal residue primitives

Chinese remaindering isolates the exact common-factor covariance. All formulas
are finite and retain the whole period; no weighted-tail replacement is made.
-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace RHTower.DeletionPeriodCovariance

/-- Residue primitive with its exact period mean removed. -/
def centeredResidue (m k : ℕ) : ℝ := (k % m : ℕ)-((m : ℝ)-1)/2

private theorem sum_blocks (f : ℕ → ℝ) (d K : ℕ) :
    (∑ n ∈ Finset.range (d*K), f n) =
      ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range d, f (d*j+i) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]

private theorem sum_period_mul {f : ℕ → ℝ} {d : ℕ}
    (hf : Function.Periodic f d) (K : ℕ) :
    (∑ n ∈ Finset.range (d*K), f n) = (K : ℝ)*∑ i ∈ Finset.range d, f i := by
  rw [sum_blocks]
  have hs (j i : ℕ) : f (d*j+i) = f i := by
    simpa only [Nat.cast_id, Nat.mul_comm, Nat.add_comm] using (hf.nat_mul j) i
  simp only [hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

private theorem periodic_of_dvd {f : ℕ → ℝ} {d P : ℕ}
    (hf : Function.Periodic f d) (hP : d ∣ P) : Function.Periodic f P := by
  obtain ⟨K,rfl⟩ := hP
  simpa only [Nat.cast_id, Nat.mul_comm] using hf.nat_mul K

/-- The centered primitive keeps its original integer period. -/
theorem centeredResidue_periodic (m : ℕ) : Function.Periodic (centeredResidue m) m := by
  intro n
  simp [centeredResidue]

private theorem sum_nat_real (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ℝ)) = (m : ℝ)*((m : ℝ)-1)/2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private theorem sum_nat_real_sq (m : ℕ) :
    (∑ i ∈ Finset.range m, (i : ℝ)^(2 : ℕ)) = (m : ℝ)*((m : ℝ)-1)*(2*(m : ℝ)-1)/6 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Exact zero mean over one complete residue period. -/
theorem sum_centeredResidue (m : ℕ) : ∑ i ∈ Finset.range m, centeredResidue m i = 0 := by
  have he : (∑ i ∈ Finset.range m, centeredResidue m i) =
      ∑ i ∈ Finset.range m, ((i : ℝ)-((m : ℝ)-1)/2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [centeredResidue, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
  rw [he, Finset.sum_sub_distrib, sum_nat_real]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The centered square moment, with no numerical evaluation of individual moduli. -/
theorem sum_centeredResidue_sq (m : ℕ) :
    (∑ i ∈ Finset.range m, centeredResidue m i^(2 : ℕ)) = (m : ℝ)*((m : ℝ)^(2 : ℕ)-1)/12 := by
  have he : (∑ i ∈ Finset.range m, centeredResidue m i^(2 : ℕ)) =
      ∑ i ∈ Finset.range m,
        ((i : ℝ)^(2 : ℕ)-((m : ℝ)-1)*(i : ℝ)+(((m : ℝ)-1)/2)^(2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [centeredResidue, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
    ring
  rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_nat_real, sum_nat_real_sq]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

private theorem mod_mul_block {g a i : ℕ} (ha : 0 < a) (hi : i < g) (j : ℕ) :
    (g*j+i) % (g*a) = g*(j%a)+i := by
  have he : g*j+i = g*(j%a)+i+(g*a)*(j/a) := by
    calc g*j+i = g*(j%a+a*(j/a))+i := by rw [Nat.mod_add_div]
         _ = _ := by ring
  rw [he, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hj := Nat.mod_lt j ha
  nlinarith

private theorem centeredResidue_mul_block {g a i : ℕ} (ha : 0 < a) (hi : i < g) (j : ℕ) :
    centeredResidue (g*a) (g*j+i) = (g : ℝ)*centeredResidue a j+centeredResidue g i := by
  rw [centeredResidue, mod_mul_block ha hi, centeredResidue, centeredResidue,
    Nat.mod_eq_of_lt hi]
  push_cast
  ring

private theorem coprime_block_covariance {g a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (i : ℕ) :
    (∑ j ∈ Finset.range (a*b),
      ((g : ℝ)*centeredResidue a j+centeredResidue g i)*
      ((g : ℝ)*centeredResidue b j+centeredResidue g i)) =
      (a : ℝ)*(b : ℝ)*centeredResidue g i^(2 : ℕ) := by
  have hf : Function.Periodic (fun j => (g : ℝ)*centeredResidue a j+centeredResidue g i) a := by
    intro j
    dsimp only
    rw [centeredResidue_periodic a j]
  have hh : Function.Periodic (fun j => (g : ℝ)*centeredResidue b j+centeredResidue g i) b := by
    intro j
    dsimp only
    rw [centeredResidue_periodic b j]
  rw [DeletionCoprimeWords.coprime_period_sum_mul ha hb hab hf hh]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_centeredResidue,
    mul_zero, zero_add, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

private theorem scaled_coprime_covariance {g a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    (∑ k ∈ Finset.range (g*(a*b)),
      centeredResidue (g*a) k*centeredResidue (g*b) k) =
      (g*(a*b) : ℕ)*((g : ℝ)^(2 : ℕ)-1)/12 := by
  rw [sum_blocks, Finset.sum_comm]
  calc _ = ∑ i ∈ Finset.range g, (a : ℝ)*(b : ℝ)*centeredResidue g i^(2 : ℕ) := by
         apply Finset.sum_congr rfl
         intro i hi
         simp_rw [centeredResidue_mul_block ha (Finset.mem_range.mp hi),
           centeredResidue_mul_block hb (Finset.mem_range.mp hi)]
         exact coprime_block_covariance ha hb hab i
       _ = _ := by rw [← Finset.mul_sum, sum_centeredResidue_sq]; push_cast; ring

/-- The complete centered pair covariance, including every shared arithmetic factor. -/
theorem sum_centeredResidue_mul {m n P : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmP : m ∣ P) (hnP : n ∣ P) :
    (∑ k ∈ Finset.range P, centeredResidue m k*centeredResidue n k) =
      (P : ℝ)*((Nat.gcd m n : ℝ)^(2 : ℕ)-1)/12 := by
  let g := Nat.gcd m n
  let a := m/g
  let b := n/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n hm
  have hma : g*a = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hnb : g*b = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  have ha : 0 < a := by nlinarith
  have hb : 0 < b := by nlinarith
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hg
  have hl : g*(a*b) = Nat.lcm m n := by
    apply Nat.eq_of_mul_eq_mul_left hg
    have h := Nat.gcd_mul_lcm m n
    change g*Nat.lcm m n = m*n at h
    nlinarith [congrArg (fun x : ℕ => x*(g*b)) hma]
  have hper : Function.Periodic
      (fun k => centeredResidue m k*centeredResidue n k) (g*(a*b)) := by
    have h1 := periodic_of_dvd (centeredResidue_periodic m) (Nat.dvd_lcm_left m n)
    have h2 := periodic_of_dvd (centeredResidue_periodic n) (Nat.dvd_lcm_right m n)
    rw [hl]
    intro k
    dsimp only
    rw [h1 k, h2 k]
  have hLP : g*(a*b) ∣ P := hl ▸ Nat.lcm_dvd hmP hnP
  obtain ⟨K,rfl⟩ := hLP
  rw [sum_period_mul hper]
  have hcore := scaled_coprime_covariance (g := g) ha hb hab
  rw [hma,hnb] at hcore
  rw [hcore]
  change _ = (((g*(a*b))*K : ℕ) : ℝ)*((g : ℝ)^(2 : ℕ)-1)/12
  push_cast
  ring

/-- A complete common period has zero centered first moment. -/
theorem sum_centeredResidue_common_period {m P : ℕ} (hmP : m ∣ P) :
    (∑ k ∈ Finset.range P, centeredResidue m k) = 0 := by
  obtain ⟨K,rfl⟩ := hmP
  rw [sum_period_mul (centeredResidue_periodic m), sum_centeredResidue, mul_zero]

/-- A literal finite real superposition of normalized residue primitives. -/
def residueCombination (S : Finset ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ S, u m*((k%m : ℕ) : ℝ)/(m : ℝ)

/-- Exact unweighted complete-period mean. -/
def periodMean (S : Finset ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, u m*((m : ℝ)-1)/(2*(m : ℝ))

/-- Full signed normalized gcd-square covariance, including every ordered pair. -/
def periodCovariance (S : Finset ℕ) (u : ℕ → ℝ) : ℝ :=
  (1/12 : ℝ)*∑ m ∈ S, ∑ n ∈ S,
    u m*u n*((Nat.gcd m n : ℝ)^(2 : ℕ)-1)/((m : ℝ)*(n : ℝ))

private theorem combination_sub_mean (S : Finset ℕ) (u : ℕ → ℝ) (k : ℕ)
    (hpos : ∀ m ∈ S, 0 < m) :
    residueCombination S u k-periodMean S u =
      ∑ m ∈ S, (u m/(m : ℝ))*centeredResidue m k := by
  rw [residueCombination, periodMean, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
  rw [centeredResidue]
  field_simp

private theorem sum_combination_sub_mean {S : Finset ℕ} (u : ℕ → ℝ) {P : ℕ}
    (hpos : ∀ m ∈ S, 0 < m) (hP : ∀ m ∈ S, m ∣ P) :
    (∑ k ∈ Finset.range P, (residueCombination S u k-periodMean S u)) = 0 := by
  simp_rw [combination_sub_mean S u _ hpos]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  rw [← Finset.mul_sum, sum_centeredResidue_common_period (hP m hm), mul_zero]

/-- Exact mean of the full finite source on any common period. -/
theorem sum_residueCombination {S : Finset ℕ} (u : ℕ → ℝ) {P : ℕ}
    (hpos : ∀ m ∈ S, 0 < m) (hP : ∀ m ∈ S, m ∣ P) :
    (∑ k ∈ Finset.range P, residueCombination S u k) = (P : ℝ)*periodMean S u := by
  have h := sum_combination_sub_mean u hpos hP
  rw [Finset.sum_sub_distrib] at h
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_eq_zero] using h

/-- Complete signed pair covariance equals the actual centered square moment. -/
theorem sum_residueCombination_centered_sq {S : Finset ℕ} (u : ℕ → ℝ) {P : ℕ}
    (hpos : ∀ m ∈ S, 0 < m) (hP : ∀ m ∈ S, m ∣ P) :
    (∑ k ∈ Finset.range P, (residueCombination S u k-periodMean S u)^(2 : ℕ)) =
      (P : ℝ)*periodCovariance S u := by
  simp_rw [combination_sub_mean S u _ hpos, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  unfold periodCovariance
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  calc _ = (u m/(m : ℝ))*(u n/(n : ℝ))*
             ∑ k ∈ Finset.range P, centeredResidue m k*centeredResidue n k := by
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro k _
         ring
       _ = _ := by
         rw [sum_centeredResidue_mul (hpos m hm) (hpos n hn) (hP m hm) (hP n hn)]
         have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
         have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos n hn
         field_simp

/-- The whole uncentered second moment splits into mean-square and signed gcd covariance. -/
theorem sum_residueCombination_sq {S : Finset ℕ} (u : ℕ → ℝ) {P : ℕ}
    (hpos : ∀ m ∈ S, 0 < m) (hP : ∀ m ∈ S, m ∣ P) :
    (∑ k ∈ Finset.range P, residueCombination S u k^(2 : ℕ)) =
      (P : ℝ)*(periodMean S u^(2 : ℕ)+periodCovariance S u) := by
  have h := sum_residueCombination_centered_sq u hpos hP
  have he : (∑ k ∈ Finset.range P, (residueCombination S u k-periodMean S u)^(2 : ℕ)) =
      (∑ k ∈ Finset.range P, residueCombination S u k^(2 : ℕ))-
        2*periodMean S u*(∑ k ∈ Finset.range P, residueCombination S u k)+
        (P : ℝ)*periodMean S u^(2 : ℕ) := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [sum_residueCombination u hpos hP] at he
  nlinarith

/-- Covariance positivity is a complete-period square identity, without a sign assumption
on individual Möbius-weighted cross terms. -/
theorem periodCovariance_nonneg {S : Finset ℕ} (u : ℕ → ℝ) {P : ℕ}
    (hpos : ∀ m ∈ S, 0 < m) (hP : ∀ m ∈ S, m ∣ P) (hP0 : 0 < P) :
    0 ≤ periodCovariance S u := by
  have h := sum_residueCombination_centered_sq u hpos hP
  have hnn : 0 ≤ ∑ k ∈ Finset.range P, (residueCombination S u k-periodMean S u)^(2 : ℕ) :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP0
  nlinarith

open ArithmeticFunction

private theorem moebius_sum_Icc (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ((moebius m : ℤ) : ℝ)) = Sieve.mertensM N := by
  rw [sum_Icc_eq_sum_range_succ, Sieve.mertensM, Finset.sum_range_succ']
  simp

/-- Exact scalar period mean of the literal Möbius primitive. -/
theorem mobius_periodMean (N : ℕ) :
    periodMean (Finset.Icc 1 N) (fun m => ((moebius m : ℤ) : ℝ)) =
      (Sieve.mertensM N-deningerHarmonicPartial N)/2 := by
  rw [periodMean, ← moebius_sum_Icc, deningerHarmonicPartial_eq_sum_Icc,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  field_simp

private theorem primitive_norm_sq (N k : ℕ) :
    ‖DeletionMobiusPrimitive.primitive N k‖^(2 : ℕ) =
      residueCombination (Finset.Icc 1 N) (fun m => ((moebius m : ℤ) : ℝ)) k^(2 : ℕ) := by
  rw [DeletionMobiusPrimitive.primitive_eq_modular, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, bdMobiusModularApproximant, neg_sq, residueCombination]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The literal Möbius primitive's complete period energy, retaining the full signed
common-factor covariance and the exact Mertens/harmonic mean. -/
theorem mobius_primitive_period_energy {N P : ℕ}
    (hP : ∀ m ∈ Finset.Icc 1 N, m ∣ P) :
    (∑ k ∈ Finset.range P, ‖DeletionMobiusPrimitive.primitive N k‖^(2 : ℕ)) =
      (P : ℝ)*(((Sieve.mertensM N-deningerHarmonicPartial N)/2)^(2 : ℕ)+
        periodCovariance (Finset.Icc 1 N) (fun m => ((moebius m : ℤ) : ℝ))) := by
  simp_rw [primitive_norm_sq]
  rw [sum_residueCombination_sq (hpos := fun m hm => (Finset.mem_Icc.mp hm).1)
    (hP := hP), mobius_periodMean]

/-- Exact full progression weight in the existing modular carrier. The zero residue
includes its nonzero multiples; its zero-index summand itself is zero. -/
def periodWeight (P r : ℕ) : ℝ :=
  ∑' j : ℕ, (1 : ℝ)/(((r+P*j : ℕ) : ℝ)*(((r+P*j : ℕ) : ℝ)+1))

private theorem stepGram_periodic {f : ℕ → ℝ} {B : ℝ} {P : ℕ}
    (hb : ∀ n, |f n| ≤ B) (hf : Function.Periodic f P) (hP : 0 < P) :
    haveI : NeZero P := ⟨hP.ne'⟩
    stepGram f f =
      ∑ r : ZMod P, f r.val^(2 : ℕ)*periodWeight P r.val := by
  letI : NeZero P := ⟨hP.ne'⟩
  let g (k : ℕ) : ℝ := f k*f k/((k : ℝ)*((k : ℝ)+1))
  have hinj : Function.Injective (fun n : ℕ => n+1) := by
    intro a b hab
    change a+1=b+1 at hab
    omega
  have hzero : ∀ k ∉ Set.range (fun n : ℕ => n+1), g k=0 := by
    intro k hk
    have hk0 : k=0 := by
      by_contra h
      exact hk ⟨k-1,by change k-1+1=k; omega⟩
    simp [hk0,g]
  have hsum : HasSum g (stepGram f f) := by
    apply (hinj.hasSum_iff hzero).mp
    have h := hasSum_stepGram hb hb
    convert h using 1
    funext n
    dsimp [g]
    push_cast
    ring
  rw [← hsum.tsum_eq, Nat.sumByResidueClasses hsum.summable P]
  apply Finset.sum_congr rfl
  intro r hr
  have he (j : ℕ) : f (r.val+P*j)=f r.val := by
    simpa only [Nat.cast_id,Nat.mul_comm] using (hf.nat_mul j) r.val
  calc (∑' j : ℕ, g (r.val+P*j)) =
         ∑' j : ℕ, f r.val^(2 : ℕ)*((1 : ℝ)/
           (((r.val+P*j : ℕ) : ℝ)*(((r.val+P*j : ℕ) : ℝ)+1))) := by
         apply tsum_congr
         intro j
         dsimp only [g]
         rw [he]
         ring
       _ = _ := tsum_mul_left

private theorem residueCombination_periodic {S : Finset ℕ} (u : ℕ → ℝ) {P : ℕ}
    (hP : ∀ m ∈ S, m ∣ P) : Function.Periodic (residueCombination S u) P := by
  intro k
  dsimp only [residueCombination]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hP m hm), Nat.add_zero, Nat.mod_mod]

private theorem combination_mobius (N k : ℕ) :
    residueCombination (Finset.Icc 1 N) (fun m => ((moebius m : ℤ) : ℝ)) k =
      -bdMobiusModularApproximant N k := by
  simp only [residueCombination,bdMobiusModularApproximant,neg_neg]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The actual full raw carrier norm retains every residue's infinite progression weight.
This is not obtained by substituting an unweighted period mean. -/
theorem mobius_modular_norm_sq_eq_weighted_period {N P : ℕ} (hP0 : 0 < P)
    (hP : ∀ m ∈ Finset.Icc 1 N, m ∣ P) :
    haveI : NeZero P := ⟨hP0.ne'⟩
    ‖bdMobiusModularApproximantVec N‖^(2 : ℕ) =
      ∑ r : ZMod P, ‖DeletionMobiusPrimitive.primitive N r.val‖^(2 : ℕ)*periodWeight P r.val := by
  have hf : Function.Periodic (bdMobiusModularApproximant N) P := by
    intro k
    have h := residueCombination_periodic (fun m => ((moebius m : ℤ) : ℝ)) hP k
    rw [combination_mobius,combination_mobius] at h
    exact neg_injective h
  have hi : (RCLike.re (inner ℂ (bdMobiusModularApproximantVec N)
      (bdMobiusModularApproximantVec N)) : ℝ) = ‖bdMobiusModularApproximantVec N‖^(2 : ℕ) :=
    inner_self_eq_norm_sq _
  rw [bdMobiusModularApproximantVec,inner_stepVec] at hi
  have hGram : stepGram (bdMobiusModularApproximant N) (bdMobiusModularApproximant N) =
      ‖bdMobiusModularApproximantVec N‖^(2 : ℕ) := hi
  rw [← hGram, stepGram_periodic (abs_bdMobiusModularApproximant_le N) hf hP0]
  apply Finset.sum_congr rfl
  intro r hr
  rw [DeletionMobiusPrimitive.primitive_eq_modular, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Unconditional complete-period second moment for every literal channel cutoff. -/
theorem mobius_primitive_factorial_energy (N : ℕ) :
    (∑ k ∈ Finset.range N.factorial, ‖DeletionMobiusPrimitive.primitive N k‖^(2 : ℕ)) =
      (N.factorial : ℝ)*(((Sieve.mertensM N-deningerHarmonicPartial N)/2)^(2 : ℕ)+
        periodCovariance (Finset.Icc 1 N) (fun m => ((moebius m : ℤ) : ℝ))) := by
  apply mobius_primitive_period_energy
  intro m hm
  exact Nat.dvd_factorial (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2

/-- The unconditional full carrier identity at every cutoff, with each factorial-period
residue carrying its actual infinite weight. -/
theorem mobius_modular_norm_sq_eq_factorial_period (N : ℕ) :
    haveI : NeZero N.factorial := ⟨(Nat.factorial_pos N).ne'⟩
    ‖bdMobiusModularApproximantVec N‖^(2 : ℕ) =
      ∑ r : ZMod N.factorial,
        ‖DeletionMobiusPrimitive.primitive N r.val‖^(2 : ℕ)*periodWeight N.factorial r.val := by
  apply mobius_modular_norm_sq_eq_weighted_period (Nat.factorial_pos N)
  intro m hm
  exact Nat.dvd_factorial (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2

end RHTower.DeletionPeriodCovariance
end
