import GaloisForLFunctions.RestrictedFactorizationCalculus.RecoveringTheMobiusPrefixFromAnIncreasingPrimeCutoff
import GaloisForLFunctions.RHTower.LocalizedHalfDensityCurvature
import GaloisForLFunctions.RHTower.CausalMobiusThetaUniformCycle

/-!
# Boolean fibres above a terminal rough tail

Strip the least prime when it lies below the current cutoff. Fixing the
last stripped prime and the stopped tail leaves every divisor of the
primorial immediately below that prime as a free factor. These fibres
are disjoint, and every complete fibre above an odd prime cancels.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The last removed prime and the surviving tail of a nontrivial fibre. -/
structure TerminalPrimeTail (b : ℕ → ℕ) (p r : ℕ) : Prop where
  prime : p.Prime
  squarefree : Squarefree r
  passes : (primorial (b r)).Coprime r
  larger : ∀ q ∈ r.primeFactors,p<q
  removed : p ≤ b (p*r)

private theorem tail_not_pass {b : ℕ → ℕ} (hb : Monotone b) {p c r : ℕ}
    (h : TerminalPrimeTail b p r) (hc : c ∣ primorial (p-1)) :
    ¬(primorial (b (p*c*r))).Coprime (p*c*r) := by
  have hpos := Nat.pos_of_dvd_of_pos hc (primorial_pos _)
  have room : p*r ≤ p*c*r := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hpos)
  have hpQ := h.prime.dvd_primorial_iff.mpr (h.removed.trans (hb room))
  have hpn : p ∣ p*c*r := (dvd_mul_right p c).trans (dvd_mul_right (p*c) r)
  exact fun co => h.prime.not_dvd_one (co ▸ Nat.dvd_gcd hpQ hpn)

private theorem earlier_prime_impossible {b : ℕ → ℕ} (hb : Monotone b) {p r c q t d : ℕ}
    (h : TerminalPrimeTail b p r) (hc : c ∣ primorial (p-1))
    (g : TerminalPrimeTail b q t) (eq : p*c*r=q*d*t) (hpq : p<q) : False := by
  have hpc : p*c ∣ primorial p := by
    rw [RHTower.primorial_prime_eq h.prime]; exact Nat.mul_dvd_mul_left p hc
  have hqQ : (primorial p).Coprime q := (g.prime.coprime_iff_not_dvd.2
    (fun bad => hpq.not_ge (g.prime.dvd_primorial_iff.1 bad))).symm
  have htQ := RHTower.coprime_primorial_of_primeFactors_gt (Nat.pos_of_ne_zero g.squarefree.ne_zero)
    (fun a ha => hpq.trans (g.larger a ha))
  have hcop := (Nat.Coprime.coprime_dvd_left hpc (hqQ.mul_right htQ)).symm
  have hd : q*t ∣ p*c*r := eq ▸ (show q*t ∣ q*d*t from ⟨d,by ring⟩)
  have hrt := hcop.dvd_of_dvd_mul_left hd
  have room := Nat.le_of_dvd (Nat.pos_of_ne_zero h.squarefree.ne_zero) hrt
  have hqsmall := g.prime.dvd_primorial_iff.2 (g.removed.trans (hb room))
  have hqr := (dvd_mul_right q t).trans hrt
  exact g.prime.not_dvd_one (h.passes ▸ Nat.dvd_gcd hqsmall hqr)

/-- Different prime–tail fibres have no integer in common, and the free
divisor within each fibre is uniquely recovered by a gcd. -/
theorem unique_terminal_prime_tail {b : ℕ → ℕ} (hb : Monotone b) {p r c q t d : ℕ}
    (h : TerminalPrimeTail b p r) (hc : c ∣ primorial (p-1))
    (g : TerminalPrimeTail b q t) (hd : d ∣ primorial (q-1))
    (eq : p*c*r=q*d*t) : p=q ∧ r=t ∧ c=d := by
  have he : p=q := le_antisymm
    (le_of_not_gt (fun hgt => earlier_prime_impossible hb g hd h eq.symm hgt))
    (le_of_not_gt (fun hlt => earlier_prime_impossible hb h hc g eq hlt))
  subst q
  have hc' := RHTower.gcd_primorial_pred_smooth_rough h.prime hc (Nat.pos_of_ne_zero h.squarefree.ne_zero) h.larger
  have hd' := RHTower.gcd_primorial_pred_smooth_rough g.prime hd (Nat.pos_of_ne_zero g.squarefree.ne_zero) g.larger
  have e : c=d := hc'.symm.trans ((congrArg (Nat.gcd (primorial (p-1))) eq).trans hd')
  subst d
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_left (Nat.mul_pos h.prime.pos (Nat.pos_of_dvd_of_pos hc (primorial_pos _))) eq,rfl⟩

/-- Every squarefree integer either passes its own test or belongs to
exactly one Boolean fibre. No fixed bound on the number of stripped
primes enters the construction. -/
theorem exists_terminal_prime_tail (b : ℕ → ℕ) (hb : Monotone b) (n : ℕ) (hs : Squarefree n) :
    (primorial (b n)).Coprime n ∨ ∃ p r c,TerminalPrimeTail b p r ∧ c ∣ primorial (p-1) ∧ n=p*c*r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases passes : (primorial (b n)).Coprime n
    · exact Or.inl passes
    have n0 := Nat.pos_of_ne_zero hs.ne_zero
    have n1 : 1<n := by
      by_contra! hn
      obtain rfl : n=1 := by omega
      exact passes (Nat.coprime_one_right _)
    let q := n.minFac
    let m := n/q
    have hq : q.Prime := Nat.minFac_prime n1.ne'
    have eq : m*q=n := Nat.div_mul_cancel (Nat.minFac_dvd _)
    have hsq := Nat.squarefree_mul_iff.mp ((congrArg Squarefree eq).mpr hs)
    have hlarger (a : ℕ) (ha : a ∈ m.primeFactors) : q<a := by
      have hd := Nat.dvd_of_mem_primeFactors ha
      have hdn : a ∣ n := eq ▸ dvd_mul_of_dvd_left hd q
      have le : q ≤ a := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors ha).two_le hdn
      exact lt_of_le_of_ne le (fun e => (hq.coprime_iff_not_dvd.mp hsq.1.symm) (e ▸ hd))
    have hqn : q ≤ b n := by
      by_contra! hh
      exact passes (RHTower.coprime_primorial_of_primeFactors_gt n0 (fun p hp => hh.trans_le
        (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le (Nat.dvd_of_mem_primeFactors hp))))
    rcases ih m (Nat.div_lt_self n0 hq.one_lt) hsq.2.1 with hm | ⟨p,r,c,tail,hc,form⟩
    · have form : q*m=n := (Nat.mul_comm ..).trans eq
      exact Or.inr ⟨q,m,1,⟨hq,hsq.2.1,hm,hlarger,by rwa [form]⟩,one_dvd _,by simpa using form.symm⟩
    · have hp : p ∣ m := form ▸ (dvd_mul_right p c).trans (dvd_mul_right (p*c) r)
      have hqp := hlarger p (Nat.mem_primeFactors.mpr ⟨tail.prime,hp,hsq.2.1.ne_zero⟩)
      have hqP := hq.dvd_primorial_iff.2 (show q ≤ p-1 by omega)
      have hcm : c ∣ m := form ▸ (Nat.dvd_mul_left c p).trans (dvd_mul_right (p*c) r)
      have hco := Nat.Coprime.coprime_dvd_left hcm hsq.1
      refine Or.inr ⟨p,r,c*q,tail,hco.mul_dvd_of_dvd_of_dvd hc hqP,?_⟩
      calc n=m*q := eq.symm
           _ = p*(c*q)*r := by rw [form]; ring

/-- The actual integers of a Boolean fibre below a sharp cutoff. -/
def terminalFibre (p r X : ℕ) :=
  (((primorial (p-1)).divisors.filter (fun c => c ≤ X/(p*r))).image (fun c => p*c*r))

theorem mem_terminalFibre {p r X n : ℕ} (hp : 0<p) (hr : 0<r) :
    n ∈ terminalFibre p r X ↔ n ≤ X ∧ ∃ c,c ∣ primorial (p-1) ∧ n=p*c*r := by
  constructor
  · intro hn
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hn
    obtain ⟨hd,hle⟩ := mem_filter.mp hc
    exact ⟨by simpa only [mul_assoc,mul_comm c p,mul_left_comm] using (Nat.le_div_iff_mul_le (Nat.mul_pos hp hr)).1 hle,
      c,(Nat.mem_divisors.mp hd).1,rfl⟩
  · rintro ⟨hn,c,hc,rfl⟩
    exact mem_image.mpr ⟨c,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hc,primorial_ne_zero _⟩,
      (Nat.le_div_iff_mul_le (Nat.mul_pos hp hr)).2 (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hn)⟩,rfl⟩

/-- Exact signed boundary charge of one fibre, including the incomplete
top divisor interval. -/
theorem signed_terminal_fibre {b : ℕ → ℕ} {p r : ℕ} (tail : TerminalPrimeTail b p r) (X : ℕ) :
    (∑ n ∈ terminalFibre p r X,(μ n:ℝ))=
      -(μ r:ℝ)*∑ c ∈ (primorial (p-1)).divisors.filter (fun c => c ≤ X/(p*r)),(μ c:ℝ) := by
  let D := (primorial (p-1)).divisors.filter (fun c => c ≤ X/(p*r))
  have hr := Nat.pos_of_ne_zero tail.squarefree.ne_zero
  have inj : Set.InjOn (fun c : ℕ => p*c*r) D := fun _ _ _ _ he =>
    Nat.eq_of_mul_eq_mul_left tail.prime.pos (Nat.eq_of_mul_eq_mul_right hr he)
  rw [terminalFibre,sum_image inj,mul_sum]
  apply sum_congr rfl
  intro c hc
  have h := RHTower.moebius_smooth_rough tail.prime (Nat.mem_divisors.mp (mem_filter.mp hc).1).1 hr tail.larger
  linarith only [h]

/-- Potential fibre labels at the sharp cutoff. -/
def terminalLabels (b : ℕ → ℕ) (X : ℕ) :=
  ((Nat.primesLE (b X)).product (Icc 1 X)).filter (fun a => TerminalPrimeTail b a.1 a.2)

private theorem complete_fibre_zero {b : ℕ → ℕ} {p r X : ℕ} (tail : TerminalPrimeTail b p r)
    (hp : 2<p) (hX : p*r*primorial (p-1) ≤ X) :
    (∑ n ∈ terminalFibre p r X,(μ n:ℝ))=0 := by
  have hpos := Nat.mul_pos tail.prime.pos (Nat.pos_of_ne_zero tail.squarefree.ne_zero)
  have all : (primorial (p-1)).divisors.filter (fun c => c ≤ X/(p*r))=(primorial (p-1)).divisors :=
    filter_eq_self.mpr (fun c hc => (Nat.le_of_dvd (primorial_pos _) (Nat.mem_divisors.mp hc).1).trans
      ((Nat.le_div_iff_mul_le hpos).2 (by rwa [mul_comm])))
  have hd := Nat.prime_two.dvd_primorial_iff.2 (show 2 ≤ p-1 by omega)
  have hne : primorial (p-1) ≠ 1 := fun he => Nat.prime_two.not_dvd_one (he ▸ hd)
  have hz : (∑ c ∈ (primorial (p-1)).divisors,(μ c:ℝ))=0 := by
    rw [RHTower.sum_divisors_moebiusCast (primorial_ne_zero _),ArithmeticFunction.one_apply_ne hne]
  rw [signed_terminal_fibre tail,all,hz,mul_zero]

/-- The whole Möbius prefix splits into the stopped tails and their
incomplete Boolean fibres. Every complete odd-prime fibre vanishes at
its own endpoint, before summing over other labels. -/
theorem sharp_boolean_fibre_decomposition (b : ℕ → ℕ) (hb : Monotone b) (X : ℕ) :
    coprimeMoebiusSum 1 X=siftedPrefix b X+
      ∑ a ∈ (terminalLabels b X).filter
        (fun a => a.1=2 ∨ X<a.1*a.2*primorial (a.1-1)),
        -(μ a.2:ℝ)*∑ c ∈ (primorial (a.1-1)).divisors.filter (fun c => c ≤ X/(a.1*a.2)),(μ c:ℝ) := by
  let J := terminalLabels b X
  let A := (Icc 1 X).filter (fun n => (primorial (b n)).Coprime n)
  let D := (Icc 1 X).filter (fun n => ¬(primorial (b n)).Coprime n)
  let V := fun a : ℕ×ℕ => terminalFibre a.1 a.2 X
  have tail {a : ℕ×ℕ} (ha : a ∈ J) : TerminalPrimeTail b a.1 a.2 := (mem_filter.mp ha).2
  have mem {a : ℕ×ℕ} (ha : a ∈ J) {n : ℕ} :
      n ∈ V a ↔ n ≤ X ∧ ∃ c,c ∣ primorial (a.1-1) ∧ n=a.1*c*a.2 :=
    mem_terminalFibre (tail ha).prime.pos (Nat.pos_of_ne_zero (tail ha).squarefree.ne_zero)
  have sub : J.biUnion V ⊆ D := by
    intro n hn
    obtain ⟨a,ha,hn⟩ := mem_biUnion.mp hn
    obtain ⟨hx,c,hc,rfl⟩ := (mem ha).1 hn
    have h0 := Nat.mul_pos (Nat.mul_pos (tail ha).prime.pos (Nat.pos_of_dvd_of_pos hc (primorial_pos _)))
      (Nat.pos_of_ne_zero (tail ha).squarefree.ne_zero)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨h0,hx⟩,tail_not_pass hb (tail ha) hc⟩
  have sumEq : (∑ n ∈ J.biUnion V,(μ n:ℝ))=∑ n ∈ D,(μ n:ℝ) := by
    apply sum_subset sub
    intro n hn hno
    obtain ⟨hi,hbad⟩ := mem_filter.mp hn
    by_contra hneg
    have hs : Squarefree n := by
      by_contra hsq
      exact hneg (by rw [moebius_eq_zero_of_not_squarefree hsq,Int.cast_zero])
    obtain ⟨p,r,c,hr,hc,he⟩ := (exists_terminal_prime_tail b hb n hs).resolve_left hbad
    have hx := (mem_Icc.mp hi).2
    have cpos := Nat.pos_of_dvd_of_pos hc (primorial_pos _)
    have hpr : p*r ≤ n := he ▸ Nat.mul_le_mul_right r (Nat.le_mul_of_pos_right _ cpos)
    have hp := hr.removed.trans (hb (hpr.trans hx))
    have hrx := (Nat.le_mul_of_pos_left r hr.prime.pos).trans (hpr.trans hx)
    have ha : (p,r) ∈ J := mem_filter.mpr ⟨mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨hp,hr.prime⟩,
      mem_Icc.mpr ⟨Nat.pos_of_ne_zero hr.squarefree.ne_zero,hrx⟩⟩,hr⟩
    exact hno (mem_biUnion.mpr ⟨(p,r),ha,(mem ha).2 ⟨hx,c,hc,he⟩⟩)
  have dis : (J:Set (ℕ×ℕ)).PairwiseDisjoint V := by
    intro a ha z hz hne
    apply disjoint_left.mpr
    intro n hna hnz
    obtain ⟨_,c,hc,he⟩ := (mem ha).1 hna
    obtain ⟨_,d,hd,he'⟩ := (mem hz).1 hnz
    obtain ⟨hp,hr,_⟩ := unique_terminal_prime_tail hb (tail ha) hc (tail hz) hd (he.symm.trans he')
    exact hne (Prod.ext hp hr)
  have split := sum_filter_add_sum_filter_not (Icc 1 X) (fun n => (primorial (b n)).Coprime n) (fun n => (μ n:ℝ))
  change (∑ n ∈ A,(μ n:ℝ))+(∑ n ∈ D,(μ n:ℝ))=∑ n ∈ Icc 1 X,(μ n:ℝ) at split
  have fixed : (∑ n ∈ A,(μ n:ℝ))=siftedPrefix b X := by
    unfold A siftedPrefix coprimeMoebiusIndicator
    rw [sum_filter]
  have full : coprimeMoebiusSum 1 X=∑ n ∈ Icc 1 X,(μ n:ℝ) := by simp [coprimeMoebiusSum,coprimeMoebiusIndicator]
  rw [full,←split,fixed,←sumEq,sum_biUnion dis]
  congr 1
  rw [sum_filter]
  apply sum_congr rfl
  intro a ha
  split_ifs with h
  · exact signed_terminal_fibre (tail ha) X
  · push_neg at h
    exact complete_fibre_zero (tail ha) (lt_of_le_of_ne (tail ha).prime.two_le h.1.symm) h.2

#print axioms exists_terminal_prime_tail
#print axioms unique_terminal_prime_tail
#print axioms signed_terminal_fibre
#print axioms sharp_boolean_fibre_decomposition

end GaloisForLFunctions.RestrictedFactorizationCalculus
