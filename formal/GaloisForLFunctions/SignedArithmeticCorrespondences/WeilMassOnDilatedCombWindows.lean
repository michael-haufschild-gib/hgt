import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheIndexOfAWindowIsFiniteAtEveryScale
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheStepPacketMatricesAtFiniteScaleHaveAnExplicitError

/-!
# The mass of Weil's form on a dilated integer comb

Common dilation preserves all prime-power contacts and divides the real
jets and the pole plane by the spacing. The diagonal gains the logarithm
of the spacing. On every fixed-ratio window, any proper integer sublattice
consequently has an arbitrarily large eventual mass floor.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Filter Topology AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart
open scoped ArithmeticFunction.vonMangoldt

/-- Moving both conductors by the same integer factor preserves each directed ratio contact. -/
def ratioContact (w : ℕ → ℝ) (m n : ℕ) : ℝ :=
  (if m ∣ n then w (n/m) else 0)+(if n ∣ m then w (m/n) else 0)

theorem ratioContact_dilate (w : ℕ → ℝ) (d : ℕ+) (m n : ℕ) :
    ratioContact w ((d:ℕ)*m) ((d:ℕ)*n) = ratioContact w m n := by
  simp only [ratioContact,Nat.mul_dvd_mul_iff_left d.pos,Nat.mul_div_mul_left _ _ d.pos]

theorem jetKernel_dilate (d : ℕ+) (m n : ℕ) :
    jetKernel ((d:ℕ)*m) ((d:ℕ)*n) = jetKernel m n/(d:ℝ) := by
  have hd : 0 < (d:ℝ) := Nat.cast_pos.mpr d.pos
  simp only [jetKernel,Nat.cast_mul,← mul_sub,← mul_add,abs_mul,abs_of_pos hd,
    div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

/-- On a common conductor the real counterterm gains exactly log d. -/
theorem counterterm_dilate (d : ℕ+) {n : ℕ} (hn : 0<n) :
    counterterm ((d:ℕ)*n) = counterterm n+Real.log d := by
  have hd : (d:ℝ) ≠ 0 := (Nat.cast_pos.mpr d.pos).ne'
  simp only [counterterm,Nat.cast_mul,mul_div_assoc,Real.log_mul hd (by positivity : (n:ℝ)/(2*Real.pi) ≠ 0)]
  exact add_comm _ _

private theorem sum_dilate (d : ℕ+) (S : Finset ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ S.image (fun m => (d:ℕ)*m), F n = ∑ m ∈ S, F ((d:ℕ)*m) :=
  sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left d.pos h)

private theorem erase_dilate (d : ℕ+) (S : Finset ℕ) (n : ℕ) :
    (S.image (fun m => (d:ℕ)*m)).erase ((d:ℕ)*n) = (S.erase n).image (fun m => (d:ℕ)*m) := by
  ext k
  simp only [mem_erase,mem_image]
  constructor
  · rintro ⟨hne,m,hm,rfl⟩
    exact ⟨m,⟨fun h => hne (h ▸ rfl),hm⟩,rfl⟩
  · rintro ⟨m,⟨hne,hm⟩,rfl⟩
    exact ⟨fun h => hne (Nat.eq_of_mul_eq_mul_left d.pos h),m,hm,rfl⟩

/-- The two poles on an image comb have one common reciprocal-spacing factor. -/
theorem pole_plane_dilate (d : ℕ+) (S : Finset ℕ) (c : ℕ → ℝ) :
    let T := S.image (fun n => (d:ℕ)*n)
    let u := fun n => c ((d:ℕ)*n)
    2*(degOne T c*degTwo T c) = 2*(degOne S u*degTwo S u)/(d:ℝ) := by
  intro T u
  simp only [T,u,degOne,degTwo,sum_dilate,Nat.cast_mul,div_eq_mul_inv,mul_inv_rev,← mul_assoc]
  rw [← sum_mul]
  ring

/-- Exact row boundary under dilation, including its diagonal counterterm. -/
theorem combPotential_dilate (d : ℕ+) (S : Finset ℕ) {n : ℕ} (hn : 0<n) :
    combPotential (S.image (fun i => (d:ℕ)*i)) ((d:ℕ)*n) =
      (∑ m ∈ S.erase n, jetKernel m n)/(d:ℝ)+(∑ m ∈ S.erase n, HodgeTheoryOfAFixedPart.contact m n)
        -counterterm n-Real.log d := by
  have hc (m : ℕ) : HodgeTheoryOfAFixedPart.contact ((d:ℕ)*m) ((d:ℕ)*n) =
      HodgeTheoryOfAFixedPart.contact m n := ratioContact_dilate (fun k => Λ k) d m n
  rw [combPotential,erase_dilate,sum_dilate,counterterm_dilate d hn]
  simp only [HodgeTheoryOfAFixedPart.pairKernel,jetKernel_dilate,hc,sum_add_distrib,sum_div]
  ring

/-- Finite-scale mass floor on any subset of the dilated window.
The only harmonic loss carries the reciprocal spacing. -/
theorem dilated_comb_floor (d : ℕ+) {N M Q : ℕ} (hN : 0<N) (hQ : N+M≤Q*N)
    {S : Finset ℕ} (hs : S ⊆ Ioc N (N+M)) (c : ℕ → ℝ) :
    let T := S.image (fun n => (d:ℕ)*n)
    (counterterm N+Real.log d-2*chebyshev Q-
      (harm M+(M:ℝ)/(4*N)+(M:ℝ)^3/(2*(N:ℝ)^3))/(d:ℝ))*
        (∑ n ∈ T, c n^2) ≤ combForm T c := by
  intro T
  let u (n : ℕ) := c ((d:ℕ)*n)
  let J := (harm M+(M:ℝ)/(4*N))/(d:ℝ)+2*chebyshev Q-counterterm N-Real.log d
  have hd : 0<(d:ℝ) := Nat.cast_pos.mpr d.pos
  have hrow {k : ℕ} (hk : k∈T) : combPotential T k ≤ J := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    have hNn := (mem_Ioc.mp (hs hn)).1
    have hlog : counterterm N ≤ counterterm n := Real.log_le_log (by positivity : 0 < (N:ℝ)/(2*Real.pi))
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hNn.le) (by positivity))
    rw [combPotential_dilate d S (hN.trans hNn)]
    dsimp only [J]
    linarith only [div_le_div_of_nonneg_right (sum_jetKernel_erase_le hN hs hn) hd.le,
      sum_contact_erase_le hN hQ hs hn,hlog]
  have hpair : combPairing T c ≤ J*∑ n ∈ T, c n^2 := by
    apply (combPairing_le_potential T c).trans
    rw [mul_sum]
    exact sum_le_sum fun n hn => (mul_le_mul_of_nonneg_left (hrow hn) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hp := div_le_div_of_nonneg_right (neg_le_two_mul_degOne_mul_degTwo hN hs u) hd.le
  have hmass : (∑ n ∈ T, c n^2) = ∑ n ∈ S, u n^2 := sum_dilate d S _
  have hpole : 2*(degOne T c*degTwo T c) = 2*(degOne S u*degTwo S u)/(d:ℝ) := pole_plane_dilate d S c
  rw [HodgeTheoryOfAFixedPart.combForm,hpole]
  rw [← hmass] at hp
  calc _ = (-((M:ℝ)^3/(2*(N:ℝ)^3))*(∑ n ∈ T, c n^2))/(d:ℝ)-J*(∑ n ∈ T, c n^2) := by
           dsimp only [J]; ring
       _ ≤ _ := sub_le_sub hp hpair

/-- Every prescribed mass floor holds eventually on every subcomb of a
properly dilated fixed-ratio window, simultaneously for all coefficients. -/
theorem eventually_dilated_comb_floor (d : ℕ+) (hd₂ : 2 ≤ (d:ℕ)) (Q : ℕ+) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ), S ⊆ Ioc N (N+(Q:ℕ)*N) → ∀ c : ℕ → ℝ,
      let T := S.image (fun n => (d:ℕ)*n)
      B*(∑ n ∈ T, c n^2) ≤ combForm T c := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let C : ℝ := 1+Real.log Q+(Q:ℝ)/4+(Q:ℝ)^3/2
  filter_upwards [eventually_ge_atTop 1,hlog.eventually_ge_atTop
    (2*(B+Real.log (2*Real.pi)+2*chebyshev ((Q:ℕ)+1)+C))] with N hN hlarge S hs c
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hq : (0:ℝ)<Q := Nat.cast_pos.mpr Q.pos
  have hd : (2:ℝ)≤d := by exact_mod_cast hd₂
  have hLd : 0 ≤ Real.log (d:ℝ) := Real.log_natCast_nonneg _
  have hcost : harm ((Q:ℕ)*N)+(((Q:ℕ)*N:ℕ):ℝ)/(4*N)+(((Q:ℕ)*N:ℕ):ℝ)^3/(2*(N:ℝ)^3) ≤
      Real.log N+C := by
    have h := harm_le_one_add_log ((Q:ℕ)*N)
    rw [Nat.cast_mul,Real.log_mul hq.ne' hn.ne'] at h
    rw [Nat.cast_mul,show (Q:ℝ)*N/(4*N)=(Q:ℝ)/4 by field_simp,
      show ((Q:ℝ)*N)^3/(2*(N:ℝ)^3)=(Q:ℝ)^3/2 by field_simp]
    dsimp only [C]
    linarith only [h]
  have hC : 0 ≤ C := by
    dsimp only [C]
    have h := Real.log_natCast_nonneg (Q:ℕ)
    positivity
  have hc := (div_le_div_of_nonneg_right hcost (by positivity : 0≤(d:ℝ))).trans
    (div_le_div_of_nonneg_left (add_nonneg (Real.log_natCast_nonneg N) hC) (by norm_num) hd)
  have h := dilated_comb_floor d hN (Q := (Q:ℕ)+1) (M := (Q:ℕ)*N)
    (by rw [Nat.succ_mul,Nat.add_comm]) hs c
  apply le_trans (mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)) h
  rw [counterterm,Real.log_div hn.ne' (by positivity)]
  dsimp only [Function.comp_apply] at hlarge
  linarith only [hc,hlarge,hLd,hC]

/-- In the full ambient window all coefficients outside the multiples of d
may be set to zero. The eventual floor is uniform on this entire subspace. -/
theorem eventually_full_comb_on_multiples (d : ℕ+) (hd : 2≤(d:ℕ)) (Q : ℕ+) (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      let W := Ioc ((d:ℕ)*N) ((d:ℕ)*(N+(Q:ℕ)*N))
      (∀ n ∈ W, ¬ (d:ℕ) ∣ n → c n=0) →
      B*(∑ n ∈ W, c n^2) ≤ combForm W c := by
  filter_upwards [eventually_dilated_comb_floor d hd Q B] with N h c
  intro W hz
  let S := Ioc N (N+(Q:ℕ)*N)
  let T := S.image (fun n => (d:ℕ)*n)
  have hsub : T ⊆ W := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hn
    obtain ⟨hl,hr⟩ := mem_Ioc.mp ha
    exact mem_Ioc.mpr ⟨Nat.mul_lt_mul_of_pos_left hl d.pos,Nat.mul_le_mul_left _ hr⟩
  have hzero (n : ℕ) (hn : n∈W) (hnt : n∉T) : c n=0 := by
    apply hz n hn
    rintro ⟨a,rfl⟩
    apply hnt
    apply mem_image.mpr
    refine ⟨a,mem_Ioc.mpr ⟨?_,?_⟩,rfl⟩
    · exact (Nat.mul_lt_mul_left d.pos).mp (mem_Ioc.mp hn).1
    · exact Nat.le_of_mul_le_mul_left (mem_Ioc.mp hn).2 d.pos
  have hm : (∑ n ∈ T, c n^2) = ∑ n ∈ W, c n^2 :=
    sum_subset hsub fun n hn hnt => by rw [hzero n hn hnt]; norm_num
  rw [combForm_of_subset hsub hzero,← hm]
  exact h S (Subset.refl _) c

#print axioms eventually_full_comb_on_multiples
#print axioms ratioContact_dilate
#print axioms combPotential_dilate
#print axioms dilated_comb_floor
#print axioms eventually_dilated_comb_floor
end GaloisForLFunctions.SignedArithmeticCorrespondences
