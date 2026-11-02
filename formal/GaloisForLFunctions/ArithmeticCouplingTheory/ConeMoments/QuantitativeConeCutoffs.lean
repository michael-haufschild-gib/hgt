import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveGridCorrection
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveAtomicConeNullseries
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TwoPrimeTowersSeeEveryOrdinateDifference
import GaloisForLFunctions.HTGeometry.SuperexponentialGrowth
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-!
# Quantitative correction schedules on two-prime cones

Square windows in two positive clocks have explicit cardinality and tail bounds.
For distinct prime logarithms, Baker separation bounds the Fourier-grid cost
polynomially in the window size. Geometric windows therefore admit correction
grids whose node counts grow at most exponentially.

The masses `exp(-4^k)` absorb every such growth rate. A fixed cutoff constant
makes each uncancelled tail small enough for the next exact positive correction.
The resulting schedule is exhaustive, has uniform finite-grid weight bounds,
and has a summable mass-weighted eighth moment of cumulative node counts.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Positive two-clock frequencies represented by a natural square. -/
def coneSquare (a b : ℝ) (N : ℕ) : Finset ℝ :=
  ((range (N+1) ×ˢ range (N+1)).image (coneFrequency a b)).erase 0

lemma mem_coneSquare_iff (a b : ℝ) (N : ℕ) (u : ℝ) :
    u ∈ coneSquare a b N ↔ u ≠ 0 ∧ ∃ m n : ℕ, m ≤ N ∧ n ≤ N ∧ coneFrequency a b (m,n)=u := by
  classical
  simp only [coneSquare, mem_erase, mem_image, mem_product, mem_range, Nat.lt_succ_iff,
    Prod.exists]
  tauto

lemma coneSquare_mono (a b : ℝ) {N M : ℕ} (hNM : N ≤ M) :
    coneSquare a b N ⊆ coneSquare a b M := by
  intro u hu
  obtain ⟨hu0, m, n, hm, hn, he⟩ := (mem_coneSquare_iff a b N u).mp hu
  exact (mem_coneSquare_iff a b M u).mpr ⟨hu0, m, n, hm.trans hNM, hn.trans hNM, he⟩

lemma coneSquare_card_le (a b : ℝ) (N : ℕ) : (coneSquare a b N).card ≤ (N+1)^2 := by
  calc
    _ ≤ ((range (N+1) ×ˢ range (N+1)).image (coneFrequency a b)).card := card_erase_le
    _ ≤ (range (N+1) ×ˢ range (N+1)).card := card_image_le
    _ = (N+1)^2 := by rw [card_product, card_range, pow_two]

lemma coneSquare_positive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {N : ℕ} {u : ℝ}
    (hu : u ∈ coneSquare a b N) : 0 < u := by
  obtain ⟨hu0, m, n, _, _, rfl⟩ := (mem_coneSquare_iff a b N u).mp hu
  exact lt_of_le_of_ne (add_nonneg (mul_nonneg (Nat.cast_nonneg m) ha.le)
    (mul_nonneg (Nat.cast_nonneg n) hb.le)) hu0.symm

lemma coneSquare_upper {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {N : ℕ} {u : ℝ}
    (hu : u ∈ coneSquare a b N) : u ≤ (N : ℝ)*(a+b) := by
  obtain ⟨_, m, n, hm, hn, rfl⟩ := (mem_coneSquare_iff a b N u).mp hu
  have hm' : (m : ℝ) ≤ N := by exact_mod_cast hm
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  dsimp only [coneFrequency]
  nlinarith only [mul_le_mul_of_nonneg_right hm' ha, mul_le_mul_of_nonneg_right hn' hb]

/-- Every newly introduced positive frequency lies beyond the old square in at least one coordinate. -/
lemma coneSquare_new_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {N M : ℕ} {u : ℝ}
    (hu : u ∈ coneSquare a b M \ coneSquare a b N) : (N : ℝ)*min a b ≤ u := by
  obtain ⟨huM, huN⟩ := mem_sdiff.mp hu
  obtain ⟨hu0, m, n, hm, hn, rfl⟩ := (mem_coneSquare_iff a b M u).mp huM
  have hout : N ≤ m ∨ N ≤ n := by
    by_contra h
    push Not at h
    exact huN ((mem_coneSquare_iff a b N _).mpr
      ⟨hu0, m, n, h.1.le, h.2.le, rfl⟩)
  dsimp only [coneFrequency]
  rcases hout with hmN | hnN
  · have hmN' : (N : ℝ) ≤ m := by exact_mod_cast hmN
    calc (N : ℝ)*min a b ≤ (N : ℝ)*a :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg N)
      _ ≤ (m : ℝ)*a := mul_le_mul_of_nonneg_right hmN' ha
      _ ≤ (m : ℝ)*a+n*b := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hb)
  · have hnN' : (N : ℝ) ≤ n := by exact_mod_cast hnN
    calc (N : ℝ)*min a b ≤ (N : ℝ)*b :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg N)
      _ ≤ (n : ℝ)*b := mul_le_mul_of_nonneg_right hnN' hb
      _ ≤ (m : ℝ)*a+n*b := le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg m) ha)

/-- A finite cardinal estimate suffices for the uncancelled exponential tail. -/
lemma coneSquare_tail_le {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 ≤ ε) (N M : ℕ) :
    ∑ u ∈ coneSquare a b M \ coneSquare a b N, Real.exp (-ε*u) ≤
      ((M : ℝ)+1)^2 * Real.exp (-ε*((N : ℝ)*min a b)) := by
  have he : ∀ u ∈ coneSquare a b M \ coneSquare a b N,
      Real.exp (-ε*u) ≤ Real.exp (-ε*((N : ℝ)*min a b)) := by
    intro u hu
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (coneSquare_new_lower ha hb hu) (neg_nonpos.mpr hε)
  calc
    _ ≤ ∑ _u ∈ coneSquare a b M \ coneSquare a b N,
        Real.exp (-ε*((N : ℝ)*min a b)) := sum_le_sum he
    _ = ((coneSquare a b M \ coneSquare a b N).card : ℝ)*
        Real.exp (-ε*((N : ℝ)*min a b)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((M : ℝ)+1)^2*Real.exp (-ε*((N : ℝ)*min a b)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast (card_le_card sdiff_subset).trans (coneSquare_card_le a b M)

/-- Correction masses decay faster than every geometric scale. -/
def correctionMass (k : ℕ) : ℝ := Real.exp (-((4 : ℝ)^k))

lemma correctionMass_pos (k : ℕ) : 0 < correctionMass k := Real.exp_pos _

lemma nat_add_one_le_four_pow (k : ℕ) : (k : ℝ)+1 ≤ (4 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith only [ih, hk]

lemma correctionMass_le_geometric (k : ℕ) : correctionMass k ≤ (1/2 : ℝ)^k := by
  have he : Real.exp (-1) ≤ (1/2 : ℝ) := by
    have h : 2 ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_neg]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ)<2) h
  calc
    correctionMass k ≤ Real.exp (-(k : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith only [nat_add_one_le_four_pow k]
    _ = (Real.exp (-1))^k := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ (1/2 : ℝ)^k := pow_le_pow_left₀ (Real.exp_pos _).le he k

lemma correctionMass_summable : Summable correctionMass :=
  Summable.of_nonneg_of_le (fun k => (correctionMass_pos k).le) correctionMass_le_geometric
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1))

lemma correctionMass_tsum_le_two : ∑' k, correctionMass k ≤ 2 := by
  have h := correctionMass_summable.tsum_le_tsum correctionMass_le_geometric
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1))
  have hs := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)<1)
  rw [hs.tsum_eq] at h
  norm_num at h
  exact h

/-- Every exponential growth rate is absorbed by the correction masses. -/
lemma summable_correctionMass_mul_pow {R : ℝ} (hR : 0 < R) :
    Summable (fun k => correctionMass k*R^k) := by
  have hfour : Tendsto (fun k : ℕ => (4 : ℝ)^k/k) atTop atTop :=
    tendsto_atTop_mono (fun k =>
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (2 : ℝ) ≤ 4) k) (Nat.cast_nonneg k))
      GaloisForLFunctions.tendsto_two_pow_div_natCast_atTop
  exact GaloisForLFunctions.summable_exp_neg_mul_pow hfour hR

/-- Every signed cone-window frequency has integer coordinates bounded by its cutoff. -/
lemma symmetric_coneSquare_coordinates (a b : ℝ) (N : ℕ) {u : ℝ}
    (hu : u ∈ symmetricSpectrum (coneSquare a b N)) :
    ∃ k l : ℤ, |(k : ℝ)| ≤ N ∧ |(l : ℝ)| ≤ N ∧ (k : ℝ)*a+l*b=u := by
  classical
  rcases mem_insert.mp hu with rfl | hu
  · exact ⟨0, 0, by simp, by simp, by simp⟩
  rcases mem_union.mp hu with hu | hu
  · obtain ⟨_, m, n, hm, hn, he⟩ := (mem_coneSquare_iff a b N u).mp hu
    refine ⟨m, n, ?_, ?_, ?_⟩
    · simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)] using
        (show (m : ℝ) ≤ N by exact_mod_cast hm)
    · simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using
        (show (n : ℝ) ≤ N by exact_mod_cast hn)
    · simpa only [Int.cast_natCast, coneFrequency] using he
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    obtain ⟨_, m, n, hm, hn, he⟩ := (mem_coneSquare_iff a b N v).mp hv
    refine ⟨-(m : ℤ), -(n : ℤ), ?_, ?_, ?_⟩
    · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)] using
        (show (m : ℝ) ≤ N by exact_mod_cast hm)
    · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using
        (show (n : ℝ) ≤ N by exact_mod_cast hn)
    · dsimp only [coneFrequency] at he
      push_cast
      linarith only [he]

/-- Baker separation controls every nonzero difference of signed cone-window frequencies. -/
lemma two_prime_coneSquare_separation {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ,
      ∀ u ∈ symmetricSpectrum (coneSquare (Real.log p) (Real.log q) N),
      ∀ v ∈ symmetricSpectrum (coneSquare (Real.log p) (Real.log q) N),
      u ≠ v → c*(2+4*(N : ℝ))^(-C) ≤ |u-v| := by
  obtain ⟨c, C, hc, hC, hsep⟩ :=
    GaloisForLFunctions.ArithmeticOfSquareRootPrecision.exists_baker_separation hp hq hpq
  refine ⟨c, C, hc, hC, ?_⟩
  intro N u hu v hv huv
  obtain ⟨k, l, hk, hl, he⟩ := symmetric_coneSquare_coordinates _ _ N hu
  obtain ⟨k', l', hk', hl', he'⟩ := symmetric_coneSquare_coordinates _ _ N hv
  have hne : l-l' ≠ 0 ∨ -(k-k') ≠ 0 := by
    by_contra h
    push Not at h
    have hll : l=l' := sub_eq_zero.mp h.1
    have hkk : k=k' := sub_eq_zero.mp (neg_eq_zero.mp h.2)
    exact huv (he.symm.trans (by simpa only [hll, hkk] using he'))
  have h := hsep (l-l') (-(k-k')) hne
  have hform : ((l-l' : ℤ) : ℝ)*Real.log q-((-(k-k') : ℤ) : ℝ)*Real.log p=u-v := by
    push_cast
    linarith only [he, he']
  rw [hform] at h
  have hheight : 2+(|((l-l' : ℤ) : ℝ)|+|((-(k-k') : ℤ) : ℝ)|) ≤ 2+4*(N : ℝ) := by
    push_cast
    rw [abs_neg]
    linarith only [abs_sub (l : ℝ) l', abs_sub (k : ℝ) k', hk, hl, hk', hl']
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by positivity) hheight (neg_nonpos.mpr hC.le)) hc.le).trans h

/-- A fixed initial cutoff constant pays for every later finite tail. -/
lemma exists_cutoff_constant {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ 68 ≤ c*C/2 ∧ (C+2)^2*Real.exp (-(c*C/2)) ≤ 1/2048 := by
  have hr : 0 < c/2 := half_pos hc
  have h0 := GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop hr 0
  have h1 := GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop hr 1
  have h2 := GaloisForLFunctions.HTGeometry.tendsto_pow_mul_exp_neg_mul_atTop hr 2
  have hlim : Tendsto (fun C : ℝ => (C+2)^2*Real.exp (-(c*C/2))) atTop (𝓝 0) := by
    have h := (h2.add (h1.const_mul 4)).add (h0.const_mul 4)
    simp only [mul_zero, add_zero] at h
    apply h.congr
    intro C
    simp only [pow_zero, pow_one, one_mul]
    rw [show c/2*C=c*C/2 by ring]
    ring
  have hsmall : ∀ᶠ C : ℝ in atTop, (C+2)^2*Real.exp (-(c*C/2)) ≤ 1/2048 :=
    (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2048))).mono fun _ h => h.le
  obtain ⟨C, hC, hC', hsmall⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and ((eventually_ge_atTop (136/c)).and hsmall)).exists
  refine ⟨C, hC, ?_, hsmall⟩
  have h := (div_le_iff₀ hc).mp hC'
  linarith only [h]

/-- The supergeometric damping absorbs the finite-square cardinal loss. -/
lemma cutoff_tail_algebra {c C : ℝ}
    (hbig : 68 ≤ c*C/2) (hsmall : (C+2)^2*Real.exp (-(c*C/2)) ≤ 1/2048)
    (k : ℕ) :
    2*((C+2)*8^(k+1))^2*Real.exp (-(c*C*4^k)) ≤ correctionMass (k+1)/16 := by
  have hpow : 1 ≤ (4 : ℝ)^k := one_le_pow₀ (by norm_num)
  have hnk : (k : ℝ) ≤ (4 : ℝ)^k := (le_add_of_nonneg_right (by norm_num)).trans
    (nat_add_one_le_four_pow k)
  have h64 : (64 : ℝ)^k ≤ Real.exp (64*(k : ℝ)) := by
    have he : (64 : ℝ) ≤ Real.exp 64 := by linarith only [Real.add_one_le_exp (64 : ℝ)]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤64) he k
    rwa [← Real.exp_nat_mul, mul_comm (k : ℝ)] at hp
  have hdec : Real.exp (-((c*C/2-4)*4^k))*(64 : ℝ)^k ≤ 1 := by
    calc
      _ ≤ Real.exp (-((c*C/2-4)*4^k))*Real.exp (64*(k : ℝ)) :=
        mul_le_mul_of_nonneg_left h64 (Real.exp_pos _).le
      _ = Real.exp (-((c*C/2-4)*4^k)+64*(k : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by
        have h := mul_le_mul_of_nonneg_right (show (64 : ℝ) ≤ c*C/2-4 by linarith only [hbig])
          (pow_nonneg (by norm_num : (0 : ℝ)≤4) k)
        nlinarith only [h, hnk])
  have hscale : (C+2)^2*Real.exp (-(c*C/2)*4^k) ≤ 1/2048 := by
    apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg (C+2))).trans hsmall
    have hp : 0 ≤ c*C/2 := by linarith only [hbig]
    nlinarith only [hpow, hp]
  have h8sq : ((8 : ℝ)^(k+1))^2=64*(64 : ℝ)^k := by
    calc ((8 : ℝ)^(k+1))^2 = ((8 : ℝ)^2)^(k+1) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = 64*(64 : ℝ)^k := by norm_num only [show (8 : ℝ)^2=64 by norm_num]; rw [pow_succ]; ring
  have hexp : Real.exp (-(c*C/2)*4^k)*Real.exp (-((c*C/2-4)*4^k))*
      correctionMass (k+1)=Real.exp (-(c*C*4^k)) := by
    rw [correctionMass, ← Real.exp_add, ← Real.exp_add, pow_succ]
    congr 1
    ring
  have he : 2*((C+2)*8^(k+1))^2*Real.exp (-(c*C*4^k)) =
      128*correctionMass (k+1)*(((C+2)^2*Real.exp (-(c*C/2)*4^k))*
        (Real.exp (-((c*C/2-4)*4^k))*(64 : ℝ)^k)) := by
    rw [mul_pow, h8sq, ← hexp]
    ring
  have hprod := mul_le_mul hscale hdec
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num : (0 : ℝ)≤64) k))
    (by norm_num : (0 : ℝ)≤1/2048)
  rw [he]
  calc
    _ ≤ 128*correctionMass (k+1)*((1/2048)*1) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (correctionMass_pos _).le)
    _ = correctionMass (k+1)/16 := by ring

/-- Explicit square cutoffs grow geometrically. -/
def quantitativeCutoff (C : ℝ) (k : ℕ) : ℕ := ⌈C*(8 : ℝ)^k⌉₊

lemma quantitativeCutoff_lower (C : ℝ) (k : ℕ) :
    C*(8 : ℝ)^k ≤ (quantitativeCutoff C k : ℝ) := Nat.le_ceil _

lemma quantitativeCutoff_upper {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    (quantitativeCutoff C k : ℝ)+1 ≤ (C+2)*(8 : ℝ)^k := by
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hC (pow_nonneg (by norm_num : (0 : ℝ)≤8) k))
  have hp : 1 ≤ (8 : ℝ)^k := one_le_pow₀ (by norm_num)
  change (⌈C*(8 : ℝ)^k⌉₊ : ℝ)+1 ≤ _
  nlinarith only [hceil, hp]

lemma quantitativeCutoff_mono {C : ℝ} (hC : 0 ≤ C) : Monotone (quantitativeCutoff C) := by
  intro k l hkl
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤8) hkl) hC

lemma quantitativeCutoff_ge {C : ℝ} (hC : 1 ≤ C) (k : ℕ) : k ≤ quantitativeCutoff C k := by
  have hp : (k : ℝ) ≤ (8 : ℝ)^k :=
    (show (k : ℝ) ≤ (4 : ℝ)^k by linarith only [nat_add_one_le_four_pow k]).trans
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4) (by norm_num : (4 : ℝ)≤8) k)
  have h := hp.trans ((le_mul_of_one_le_left (pow_nonneg (by norm_num : (0 : ℝ)≤8) k) hC).trans
    (quantitativeCutoff_lower C k))
  exact_mod_cast h

/-- The explicit square windows exhaust the natural cone. -/
lemma quantitativeCutoff_covers {a b C : ℝ} (hC : 1 ≤ C) (t : PositiveCone a b) :
    ∃ k, t.val ∈ coneSquare a b (quantitativeCutoff C k) := by
  obtain ⟨⟨m,n⟩, he⟩ := t.property.2
  let k := max m n
  refine ⟨k, (mem_coneSquare_iff a b _ _).mpr ⟨t.property.1.ne', m, n, ?_, ?_, he⟩⟩
  · exact (le_max_left m n).trans (quantitativeCutoff_ge hC k)
  · exact (le_max_right m n).trans (quantitativeCutoff_ge hC k)

/-- Geometric level gaps and explicit square cutoffs satisfy the positive-correction threshold. -/
theorem exists_quantitative_tail_schedule {a b d D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hdD : d < D) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ,
      2*∑ u ∈ coneSquare a b (quantitativeCutoff C (k+1)) \ coneSquare a b (quantitativeCutoff C k),
        Real.exp (-((D-d)/2*(1/2 : ℝ)^k)*u) ≤ correctionMass (k+1)/16 := by
  let c : ℝ := (D-d)/2*min a b
  have hc : 0 < c := mul_pos (half_pos (sub_pos.mpr hdD)) (lt_min ha hb)
  obtain ⟨C, hC, hbig, hsmall⟩ := exists_cutoff_constant hc
  refine ⟨C, hC, ?_⟩
  intro k
  let N := quantitativeCutoff C k
  let M := quantitativeCutoff C (k+1)
  let ε := (D-d)/2*(1/2 : ℝ)^k
  have hε : 0 ≤ ε := mul_nonneg (half_pos (sub_pos.mpr hdD)).le (pow_nonneg (by norm_num) k)
  have hexponent : c*C*(4 : ℝ)^k ≤ ε*((N : ℝ)*min a b) := by
    have h := mul_le_mul_of_nonneg_left (quantitativeCutoff_lower C k)
      (mul_nonneg hε (le_min ha.le hb.le))
    have he : ε*min a b*(C*(8 : ℝ)^k)=c*C*(4 : ℝ)^k := by
      dsimp only [ε, c]
      have hp : (1/2 : ℝ)^k*(8 : ℝ)^k=(4 : ℝ)^k := by rw [← mul_pow]; norm_num
      calc
        (D-d)/2*(1/2 : ℝ)^k*min a b*(C*(8 : ℝ)^k) =
            ((D-d)/2*min a b)*C*((1/2 : ℝ)^k*(8 : ℝ)^k) := by ring
        _ = _ := by rw [hp]
    rw [he] at h
    nlinarith only [h]
  have hexp : Real.exp (-ε*((N : ℝ)*min a b)) ≤ Real.exp (-(c*C*4^k)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hexponent]
  have hcard := quantitativeCutoff_upper (show 0 ≤ C by linarith only [hC]) (k+1)
  have hcard2 : ((M : ℝ)+1)^2 ≤ ((C+2)*8^(k+1))^2 :=
    pow_le_pow_left₀ (by positivity) hcard 2
  have htail := coneSquare_tail_le ha.le hb.le hε N M
  have hmajor := mul_le_mul hcard2 hexp (Real.exp_pos _).le (sq_nonneg _)
  have hfull := mul_le_mul_of_nonneg_left (htail.trans hmajor) (by norm_num : (0 : ℝ)≤2)
  calc
    _ ≤ 2*(((C+2)*8^(k+1))^2*Real.exp (-(c*C*4^k))) := hfull
    _ = 2*((C+2)*8^(k+1))^2*Real.exp (-(c*C*4^k)) := by ring
    _ ≤ correctionMass (k+1)/16 := cutoff_tail_algebra hbig hsmall k

lemma symmetricSpectrum_card_le (S : Finset ℝ) :
    (symmetricSpectrum S).card ≤ 2*S.card+1 := by
  classical
  have hI : (symmetricSpectrum S).card ≤ (S ∪ S.image Neg.neg).card+1 := card_insert_le _ _
  have hU := card_union_le S (S.image Neg.neg)
  have hN : (S.image Neg.neg).card ≤ S.card := card_image_le
  omega

lemma symmetric_coneSquare_card_le (a b : ℝ) (N : ℕ) :
    ((symmetricSpectrum (coneSquare a b N)).card : ℝ) ≤ 3*((N : ℝ)+1)^2 := by
  have h := (symmetricSpectrum_card_le (coneSquare a b N)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (coneSquare_card_le a b N)) 1)
  have h' : ((symmetricSpectrum (coneSquare a b N)).card : ℝ) ≤ 2*((N : ℝ)+1)^2+1 := by
    exact_mod_cast h
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith only [h', hN]

lemma symmetricSpectrum_radius (S : Finset ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hS : ∀ u ∈ S, |u| ≤ L) : ∀ u ∈ symmetricSpectrum S, |u| ≤ L := by
  classical
  intro u hu
  rcases mem_insert.mp hu with rfl | hu
  · simpa only [abs_zero] using hL
  rcases mem_union.mp hu with hu | hu
  · exact hS u hu
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    simpa only [abs_neg] using hS v hv

lemma symmetric_coneSquare_radius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    ∀ u ∈ symmetricSpectrum (coneSquare a b N), |u| ≤ (a+b+1)*((N : ℝ)+1) := by
  apply symmetricSpectrum_radius _ (by positivity)
  intro u hu
  rw [abs_of_pos (coneSquare_positive ha hb hu)]
  have h := coneSquare_upper ha.le hb.le hu
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith only [h, ha, hb, hN]

lemma rpow_nat_power (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (s : ℝ) :
    (x^k)^s=(x^s)^k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

/-- Polynomial Fourier-grid costs become exponential along the explicit cutoff schedule. -/
lemma exists_grid_cost_geometric_bound {a b c B C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hB : 0 ≤ B) (hC : 1 ≤ C) :
    ∃ U R : ℝ, 0 < U ∧ 1 < R ∧ ∀ k : ℕ,
      16*((symmetricSpectrum (coneSquare a b (quantitativeCutoff C k))).card : ℝ)*
        ((a+b+1)*((quantitativeCutoff C k : ℝ)+1))/
        (c*(2+4*(quantitativeCutoff C k : ℝ))^(-B))+1 ≤ U*R^k := by
  let Q := C+2
  let V := (48*(a+b+1)/c)*Q^3*(4*Q)^B
  let R := 1+512*(8 : ℝ)^B
  have hQ : 0 < Q := by dsimp only [Q]; linarith only [hC]
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hR : 1 < R := by
    have hpos : 0 < 512*(8 : ℝ)^B := by positivity
    dsimp only [R]
    linarith only [hpos]
  refine ⟨V+1, R, by positivity, hR, ?_⟩
  intro k
  let N := quantitativeCutoff C k
  let X := (N : ℝ)+1
  have hX : 0 < X := by dsimp only [X]; positivity
  have hbase : 0 < 2+4*(N : ℝ) := by positivity
  have hNX : X ≤ Q*(8 : ℝ)^k := quantitativeCutoff_upper (by linarith only [hC]) k
  have h2N : 2+4*(N : ℝ) ≤ 4*(Q*(8 : ℝ)^k) := by
    dsimp only [X] at hNX
    linarith only [hNX]
  have hcard := symmetric_coneSquare_card_le a b N
  have hden : 0 < c*(2+4*(N : ℝ))^(-B) := mul_pos hc (Real.rpow_pos_of_pos hbase _)
  have hmain : 16*((symmetricSpectrum (coneSquare a b N)).card : ℝ)*((a+b+1)*X)/
      (c*(2+4*(N : ℝ))^(-B)) ≤ V*R^k := by
    calc
      _ ≤ 16*(3*X^2)*((a+b+1)*X)/(c*(2+4*(N : ℝ))^(-B)) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) (by positivity)
      _ = (48*(a+b+1)/c)*X^3*(2+4*(N : ℝ))^B := by
        rw [Real.rpow_neg hbase.le]
        field_simp [hc.ne', (Real.rpow_pos_of_pos hbase B).ne']
        ring
      _ ≤ (48*(a+b+1)/c)*(Q*(8 : ℝ)^k)^3*(4*(Q*(8 : ℝ)^k))^B := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX.le hNX 3) (by positivity)
        · exact Real.rpow_le_rpow hbase.le h2N hB
        · positivity
        · positivity
      _ = V*(512*(8 : ℝ)^B)^k := by
        rw [show 4*(Q*(8 : ℝ)^k)=(4*Q)*(8 : ℝ)^k by ring,
          Real.mul_rpow (by positivity : 0 ≤ 4*Q) (pow_nonneg (by norm_num : (0 : ℝ)≤8) k),
          rpow_nat_power 8 (by norm_num) k B, mul_pow]
        dsimp only [V]
        rw [mul_pow]
        have hp : ((8 : ℝ)^k)^3=(512 : ℝ)^k := by
          rw [← pow_mul, Nat.mul_comm k 3, pow_mul]
          norm_num
        rw [hp]
        ring
      _ ≤ V*R^k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by dsimp only [R]; linarith) k) hV
  have h1 : (1 : ℝ) ≤ R^k := one_le_pow₀ hR.le
  dsimp only [N, X] at hmain
  nlinarith only [hmain, h1]

/-- Cumulative node counts are the ranks used in height placement. -/
def gridPrefixSize (n : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ range (k+1), n j

lemma gridPrefixSize_pos {n : ℕ → ℕ} (hn : ∀ k, 0 < n k) (k : ℕ) :
    0 < gridPrefixSize n k := by
  have h : n k ≤ gridPrefixSize n k :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_self k))
  exact (hn k).trans_le h

lemma gridPrefixSize_geometric_bound {n : ℕ → ℕ} {U R : ℝ}
    (hU : 0 ≤ U) (hR : 1 ≤ R) (hn : ∀ k, (n k : ℝ) ≤ U*R^k) (k : ℕ) :
    (gridPrefixSize n k : ℝ) ≤ U*(4*R)^k := by
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  calc
    (gridPrefixSize n k : ℝ) = ∑ j ∈ range (k+1), (n j : ℝ) := by rw [gridPrefixSize, Nat.cast_sum]
    _ ≤ ∑ _j ∈ range (k+1), U*R^k := by
      apply sum_le_sum
      intro j hj
      exact (hn j).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hR (Nat.le_of_lt_succ (mem_range.mp hj))) hU)
    _ = ((k : ℝ)+1)*(U*R^k) := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ ≤ (4 : ℝ)^k*(U*R^k) :=
      mul_le_mul_of_nonneg_right (nat_add_one_le_four_pow k) (mul_nonneg hU (pow_nonneg hR0 k))
    _ = U*(4*R)^k := by rw [mul_pow]; ring

/-- Supergeometric masses absorb the eighth moment of all prefix counts. -/
lemma summable_weighted_prefix_count {n : ℕ → ℕ} {U R : ℝ}
    (hU : 0 < U) (hR : 1 < R) (hn : ∀ k, (n k : ℝ) ≤ U*R^k) :
    Summable (fun k => correctionMass k*(gridPrefixSize n k : ℝ)^8) := by
  have hR0 : 0 < R := lt_trans (by norm_num) hR
  have hbase : 0 < (4*R)^8 := by positivity
  have hs := (summable_correctionMass_mul_pow hbase).mul_left (U^8)
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (correctionMass_pos k).le
    (pow_nonneg (Nat.cast_nonneg (gridPrefixSize n k)) 8)) _ hs
  intro k
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (gridPrefixSize n k))
    (gridPrefixSize_geometric_bound hU.le hR.le hn k) 8
  have h := mul_le_mul_of_nonneg_left hpow (correctionMass_pos k).le
  calc
    correctionMass k*(gridPrefixSize n k : ℝ)^8 ≤ correctionMass k*(U*(4*R)^k)^8 := h
    _ = U^8*(correctionMass k*((4*R)^8)^k) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 8, pow_mul]
      ring

/-- Finite positive corrections with controlled size, exhaustive moments, and summably small masses. -/
structure PositiveGridSchedule (a b d D : ℝ) where
  frequency : ℕ → Finset ℝ
  size : ℕ → ℕ
  radius : ℕ → ℝ
  size_pos : ∀ k, 0 < size k
  radius_one_le : ∀ k, 1 ≤ radius k
  positive : ∀ k u, u ∈ frequency k → 0 < u
  nested : ∀ k l, k ≤ l → frequency k ⊆ frequency l
  covers : ∀ t : PositiveCone a b, ∃ k, t.val ∈ frequency k
  correct : ∀ k (A : ℝ), 0 < A → ∀ r : ℝ → ℂ,
    (∑ u ∈ frequency k, ‖r u‖) ≤ A/16 → ∀ H : ℝ, ∃ w : Fin (size k) → ℝ,
      (∀ j, 0 < w j ∧ A/(2*size k) ≤ w j ∧ w j ≤ 3*A/(2*size k)) ∧
      (∑ j, w j=A) ∧
      (∀ u ∈ frequency k, ∑ j, (w j : ℂ)*phase u (H+j.val*(Real.pi/(2*radius k))) = -r u)
  size_growth : ∃ U R : ℝ, 0 < U ∧ 1 < R ∧ ∀ k, (size k : ℝ) ≤ U*R^k
  tail : ∀ k, 2*∑ u ∈ frequency (k+1) \ frequency k,
    Real.exp (-(approachLevel d D (k+1)-approachLevel d D k)*u) ≤ correctionMass (k+1)/16

/-- Prime logarithms admit an exhaustive positive-correction schedule with exponential size growth. -/
theorem exists_two_prime_grid_schedule {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {d D : ℝ} (hdD : d < D) : Nonempty (PositiveGridSchedule (Real.log p) (Real.log q) d D) := by
  classical
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨C, hC, htail⟩ := exists_quantitative_tail_schedule ha hb hdD
  obtain ⟨c, B, hc, hB, hsep⟩ := two_prime_coneSquare_separation hp hq hpq
  let S := fun k => coneSquare (Real.log p) (Real.log q) (quantitativeCutoff C k)
  let L := fun k => (Real.log p+Real.log q+1)*((quantitativeCutoff C k : ℝ)+1)
  let σ := fun k => c*(2+4*(quantitativeCutoff C k : ℝ))^(-B)
  have hL : ∀ k, 1 ≤ L k := by
    intro k
    have hN : (0 : ℝ) ≤ quantitativeCutoff C k := Nat.cast_nonneg _
    dsimp only [L]
    have hprod : 0 ≤ (Real.log p+Real.log q+1)*(quantitativeCutoff C k : ℝ) :=
      mul_nonneg (by linarith only [ha, hb]) hN
    nlinarith only [ha, hb, hprod]
  have hσ : ∀ k, 0 < σ k := by intro k; dsimp only [σ]; positivity
  have hgrids : ∀ k, ∃ n : ℕ, 0 < n ∧
      (n : ℝ) ≤ 16*((symmetricSpectrum (S k)).card : ℝ)*L k/σ k+1 ∧
      ∀ A : ℝ, 0 < A → ∀ r : ℝ → ℂ, (∑ u ∈ S k, ‖r u‖) ≤ A/16 →
      ∀ H : ℝ, ∃ w : Fin n → ℝ,
        (∀ j, 0 < w j ∧ A/(2*n) ≤ w j ∧ w j ≤ 3*A/(2*n)) ∧
        (∑ j, w j=A) ∧
        (∀ u ∈ S k, ∑ j, (w j : ℂ)*phase u (H+j.val*(Real.pi/(2*L k))) = -r u) := by
    intro k
    exact exists_positive_grid_correction (S k) (fun _ hu => coneSquare_positive ha hb hu)
      (lt_of_lt_of_le (by norm_num) (hL k)) (hσ k)
      (symmetric_coneSquare_radius ha hb _) (hsep _)
  choose n hn hnsize hcorrect using hgrids
  obtain ⟨U, R, hU, hR, hcost⟩ := exists_grid_cost_geometric_bound ha hb hc hB.le hC
  refine ⟨{
    frequency := S
    size := n
    radius := L
    size_pos := hn
    radius_one_le := hL
    positive := fun _ _ hu => coneSquare_positive ha hb hu
    nested := fun _ _ h => coneSquare_mono _ _ (quantitativeCutoff_mono (by linarith only [hC]) h)
    covers := quantitativeCutoff_covers hC
    correct := hcorrect
    size_growth := ⟨U, R, hU, hR, fun k => (hnsize k).trans (hcost k)⟩
    tail := ?_
  }⟩
  intro k
  have he : approachLevel d D (k+1)-approachLevel d D k=(D-d)/2*(1/2 : ℝ)^k := by
    simp only [approachLevel, pow_succ]
    ring
  rw [he]
  exact htail k

#print axioms exists_two_prime_grid_schedule

#print axioms summable_weighted_prefix_count
#print axioms correctionMass_tsum_le_two
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
