/-
Width schedules adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.CanonicalCharactersAndLossParameters

/-!
# Width schedules

Scales, widths, counts and reserves of the centered-moment energy width schedule; lower
profiles, width ranges and capped requests with their admission conditions.
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
open scoped Classical BigOperators

namespace CenteredMomentEnergyWidthSchedule
open CenteredMomentSuccessorPaidParameters CenteredMomentFirstSecondLossParameters

def amplification (ε:ℝ):ℝ := min 1 (ε/16000)
def count (M ε:ℝ):ℕ := depth M (amplification ε)
def scale (M B ε:ℝ):ℝ := (count M ε:ℝ)+M+10*B+30
def reserve (M B ε:ℝ):ℝ :=
  min (amplification ε/100) (ε/(1000000*scale M B ε))
def mesh (M B κ ε:ℝ):ℝ := reserve M B ε/(κ+1)
def width (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε/16+(k:ℝ)*amplification ε/2
def loss (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε+64*(k:ℝ)*reserve M B ε

theorem bounds (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε):
    0< amplification ε ∧ amplification ε≤1 ∧ amplification ε≤ε/16000 ∧
    0< reserve M B ε ∧ 0< mesh M B κ ε ∧ mesh M B κ ε≤ reserve M B ε ∧
    κ*mesh M B κ ε≤ reserve M B ε ∧
    20*reserve M B ε≤ amplification ε/2 ∧
    M< width M B ε (count M ε) ∧
    loss M B ε (count M ε)≤ε/1000 :=by
  have hs:0< amplification ε:=lt_min (by norm_num) (by positivity)
  have hs1:amplification ε≤1:=min_le_left _ _
  have hse:amplification ε≤ε/16000:=min_le_right _ _
  have hn:0≤(count M ε:ℝ):=Nat.cast_nonneg _
  have hL:0< scale M B ε:=by unfold scale;positivity
  have hr:0< reserve M B ε:=lt_min (by positivity) (by positivity)
  have hrs:reserve M B ε≤ amplification ε/100:=min_le_left _ _
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hnL:(count M ε:ℝ)≤ scale M B ε:=by unfold scale;linarith
  have h1L:1≤ scale M B ε:=by unfold scale;linarith
  have hnR:(count M ε:ℝ)*reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right hnL hr.le
    nlinarith
  have hR:reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right h1L hr.le
    nlinarith
  have hm:0< mesh M B κ ε:=by unfold mesh;positivity
  have hmr:mesh M B κ ε≤ reserve M B ε:=by
    unfold mesh
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm:κ*mesh M B κ ε≤ reserve M B ε:=mesh_cost κ _ hκ hr.le
  have hw:M< width M B ε (count M ε):=by
    have hd:=depth_covers M (amplification ε) hs
    change M<(count M ε:ℝ)*amplification ε/2 at hd
    unfold width
    linarith
  refine ⟨hs,hs1,hse,hr,hm,hmr,hkm,by linarith,hw,?_⟩
  unfold loss
  linarith

lemma reserve_cost (M B ε c:ℝ)(hM:0≤ M)(hB:0≤ B)(hε:0<ε)
    (hc:c≤ scale M B ε):c*reserve M B ε≤ε/1000000:=by
  have hL:0< scale M B ε:=by unfold scale;positivity
  have hs:0< amplification ε:=lt_min (by norm_num) (by positivity)
  have hr:0< reserve M B ε:=lt_min (by positivity) (by positivity)
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hh:=mul_le_mul_of_nonneg_right hc hr.le
  nlinarith

theorem one_time_losses (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)
    (df es d theta other A:ℝ)(hdf:df≤ reserve M B ε)(hes:es≤ reserve M B ε)
    (hd:d≤ reserve M B ε)(ht:theta≤ reserve M B ε)(ho:other≤ reserve M B ε)
    (he0:0≤ es)(hA:A≤ M):
    exceptional (amplification ε) df es d B theta≤ε/1000 ∧
      diagonal (amplification ε) d other es A≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hs:=hb.2.2.1
  have hr:=hb.2.2.2.1
  have hx:=reserve_cost M B ε (10*B+7) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have hy:=reserve_cost M B ε (M+2) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have htheta:=mul_le_mul_of_nonneg_left ht (show 0≤2*(5*B+1) by positivity)
  have hmul:es*A≤ reserve M B ε*M:=
    (mul_le_mul_of_nonneg_left hA he0).trans (mul_le_mul_of_nonneg_right hes hM)
  constructor
  · unfold exceptional
    nlinarith
  · unfold CenteredMomentSuccessorPaidParameters.diagonal
    nlinarith

lemma mesh_lt_prime_width (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε):
    mesh M B κ ε< amplification ε/6:=by
  have h:=bounds M B κ ε hM hB hκ hε
  have hp:=h.1
  have hm:=h.2.2.2.2.2.1
  have hr:=h.2.2.2.2.2.2.2.1
  linarith

lemma width_zero (M B ε:ℝ):width M B ε 0=reserve M B ε/16:=by simp [width]
lemma loss_zero (M B ε:ℝ):loss M B ε 0=reserve M B ε:=by simp [loss]
lemma width_succ (M B ε:ℝ)(k:ℕ):
    width M B ε (k+1)-amplification ε/2=width M B ε k:=by
  simp only [width,Nat.cast_add,Nat.cast_one]
  ring
lemma loss_succ (M B ε:ℝ)(k:ℕ):
    loss M B ε (k+1)=loss M B ε k+64*reserve M B ε:=by
  simp only [loss,Nat.cast_add,Nat.cast_one]
  ring

lemma child_band (M B ε parent child:ℝ)(k:ℕ)
    (hp:parent≤ width M B ε (k+1))(hc:child≤ parent-amplification ε/2):
    child≤ width M B ε k:=by
  rw [←width_succ M B ε k]
  linarith

lemma loss_le_final (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤ count M ε):loss M B ε k≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hk':(k:ℝ)≤(count M ε:ℝ):=by exact_mod_cast hk
  apply le_trans _ hb.2.2.2.2.2.2.2.2.2
  unfold loss
  gcongr

lemma next_paid_loss (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other:ℝ)
    (her:er≤ reserve M B ε)(hd:d≤ reserve M B ε)(he:e≤ reserve M B ε)
    (hd1:d1≤ reserve M B ε)(hd2:d2≤ reserve M B ε)(ht:theta≤ reserve M B ε)
    (ho:other≤50*reserve M B ε):
    loss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+other≤
      loss M B ε (k+1):=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hm:=hb.2.2.2.2.2.2.1
  rw [loss_succ]
  unfold edge
  linarith

theorem actual_removal_path {ι:Type*}[DecidableEq ι]
    (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0<κ)(hε:0<ε)
    (n:ℕ)(J:Fin n→Finset ι)(w:Fin n→ι→ℝ)(x y state:Fin n→ℝ)
    (hw:∀k,∀i∈J k,0≤ w k i)(hm:∀k,∀i∈J k,w k i≤ mesh M B κ ε):
    ∃R:Fin n→Finset ι,(∀k,R k⊆J k) ∧
      (∀k,R k=J k ∨ x k+y k+6*κ*(∑i∈J k\R k,w k i)≤ state k) ∧
      (∑k,κ*(∑i∈R k,w k i))≤
        (∑k,CenteredMomentLiveCapacity.excess (J k) (w k) (x k) (y k) (state k) κ/6)+
          (n:ℝ)*reserve M B ε:=by
  have hb:=bounds M B κ ε hM hB hκ.le hε
  have hmesh:=hb.2.2.2.2.1
  have hcost:=hb.2.2.2.2.2.2.1
  choose R hR hcap hpay using fun k=> CenteredMomentLiveCapacity.removal_excess_cost
    (J k) (w k) (x k) (y k) (state k) κ (mesh M B κ ε) hκ hmesh.le (hw k) (hm k)
  refine ⟨R,hR,hcap,?_⟩
  calc
    _≤∑k,(CenteredMomentLiveCapacity.excess (J k) (w k) (x k) (y k) (state k) κ/6+
        reserve M B ε):=Finset.sum_le_sum (fun k _=>(hpay k).trans (by linarith))
    _=_:=by rw [Finset.sum_add_distrib];simp

end CenteredMomentEnergyWidthSchedule

end

noncomputable section
namespace CenteredMomentEnergyProfiles
def lower (a b:ℝ):ℕ→ℝ
  | 0=> a
  | n+1=> lower a b n/max 1 b

lemma lower_pos (a b:ℝ)(ha:0< a)(n:ℕ):0< lower a b n:=by
  induction n with
  | zero=> exact ha
  | succ n ih=> exact div_pos ih (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

lemma lower_antitone (a b:ℝ)(ha:0< a):Antitone (lower a b):=by
  apply antitone_nat_of_succ_le
  intro n
  exact div_le_self (lower_pos a b ha n).le (le_max_left _ _)


end CenteredMomentEnergyProfiles
end

noncomputable section

namespace CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

def step (M B L:ℝ):ℝ:=4*(L+M+B+4)
def range (M B L:ℝ):ℕ→ℝ
  | 0=> max 1 L
  | n+1=> step M B (range M B L n)
def sourceCap (M B L:ℝ)(n:ℕ):ℝ:=10*(range M B L n+M+B+1)
def finalSourceCap (M B L ε:ℝ):ℝ:=sourceCap M B L (count M ε)
def fineMesh (M B L κ ε:ℝ):ℝ:=mesh M (finalSourceCap M B L ε) κ ε

lemma range_nonneg (M B L:ℝ)(hM:0≤ M)(hB:0≤ B)(n:ℕ):0≤ range M B L n:=by
  induction n with
  | zero=> exact zero_le_one.trans (le_max_left _ _)
  | succ n ih=> simp only [range,step];positivity

lemma range_mono (M B L:ℝ)(hM:0≤ M)(hB:0≤ B):Monotone (range M B L):=by
  apply monotone_nat_of_le_succ
  intro n
  have hh:=range_nonneg M B L hM hB n
  simp only [range,step]
  linarith

lemma range_original (M B L:ℝ)(hM:0≤ M)(hB:0≤ B)(n:ℕ):L≤ range M B L n:=by
  exact (le_max_right (1:ℝ) L).trans (range_mono M B L hM hB (Nat.zero_le n))

lemma step_admits (M B L rho d e:ℝ)(hM:0≤ M)(hB:0≤ B)(hL:0≤ L)
    (hrho:rho≤1)(hd:d≤1)(he:e≤1):
    L≤ step M B L ∧ M+B+rho/100+1≤ step M B L ∧
    max L (M+B+2*d)+1≤ step M B L ∧
    2*L+e≤ step M B L ∧
    2*(max L (M+B+2*d)+1)+e≤ step M B L:=by
  have hmax:max L (M+B+2*d)≤ L+M+B+2:=by
    apply max_le <;> linarith
  unfold step
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma range_envelope (M B L:ℝ)(hM:0≤ M)(hB:0≤ B)(n:ℕ):
    range M B L n≤(8:ℝ)^n*(max 1 L+M+B+4):=by
  induction n with
  | zero=> simp only [range,pow_zero,one_mul];linarith
  | succ n ih=>
    have hp:1≤(8:ℝ)^n:=one_le_pow₀ (by norm_num)
    have ha:0≤ max 1 L:=zero_le_one.trans (le_max_left _ _)
    have hm:M+B+4≤(8:ℝ)^n*(max 1 L+M+B+4):=by
      have hh:=mul_le_mul_of_nonneg_right hp (show 0≤ max 1 L+M+B+4 by positivity)
      simp only [one_mul] at hh
      linarith
    simp only [range,step,pow_succ]
    nlinarith

lemma ready_exponent_le (M B L A D P q e xi:ℝ)(n:ℕ)
    (hM:0≤ M)(hB:0≤ B)
    (hA:A≤2*range M B L n+M+1)(hD:D≤1)(hP:P≤ B)
    (hq:q≤4*range M B L n+3*M+4)(he:e≤1)(hxi:xi≤1):
    CenteredMomentFirstSecondInputGates.exponent A D P q e xi≤ sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold CenteredMomentFirstSecondInputGates.exponent sourceCap
  apply max_le
  · linarith
  apply max_le
  · linarith
  apply max_le <;> linarith

lemma sourceCap_nonneg (M B L:ℝ)(hM:0≤ M)(hB:0≤ B)(n:ℕ):0≤ sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold sourceCap
  positivity

lemma fineMesh_pos (M B L κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε):
    0< fineMesh M B L κ ε:=by
  exact (bounds M (finalSourceCap M B L ε) κ ε hM
    (sourceCap_nonneg M B L hM hB _) hκ hε).2.2.2.2.1

lemma support_step (a b:ℝ)(ha:0< a)(n:ℕ):
    0< lower a b (n+1) ∧ lower a b (n+1)=lower a b n/max 1 b:=
  ⟨lower_pos a b ha _,rfl⟩

end CenteredMomentEnergyWidthRanges

end

noncomputable section

namespace CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentSuccessorPaidParameters

def stageLoss (M B ε:ℝ)(k:ℕ):ℝ:=ε/1000+loss M B ε k

lemma stageLoss_pos (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0< stageLoss M B ε k:=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  unfold stageLoss loss
  positivity

lemma stageLoss_final (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤ count M ε):stageLoss M B ε k≤ε/500:=by
  have hh:=loss_le_final M B κ ε hM hB hκ hε k hk
  unfold stageLoss
  linarith

lemma successor_with_references (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other highReflection zeroReflection:ℝ)
    (her:er≤ reserve M B ε)(hd:d≤ reserve M B ε)(he:e≤ reserve M B ε)
    (hd1:d1≤ reserve M B ε)(hd2:d2≤ reserve M B ε)(ht:theta≤ reserve M B ε)
    (ho:other≤48*reserve M B ε)
    (hhigh:highReflection≤ reserve M B ε)(hzero:zeroReflection≤ reserve M B ε):
    stageLoss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+
      other+highReflection+zeroReflection≤ stageLoss M B ε (k+1):=by
  have hh:=next_paid_loss M B κ ε hM hB hκ hε k er d e d1 d2 theta
    (other+highReflection+zeroReflection) her hd he hd1 hd2 ht (by linarith)
  unfold stageLoss
  linarith

lemma one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(sourceLoss extra:ℝ)(hsource:sourceLoss≤ε/1000)
    (hextra:extra≤50*reserve M B ε):
    sourceLoss+extra≤ stageLoss M B ε (k+1):=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have hk:0≤(k:ℝ):=Nat.cast_nonneg _
  simp only [stageLoss,loss,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma actual_one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(df es d theta other A extra:ℝ)
    (hdf:df≤ reserve M B ε)(hes:es≤ reserve M B ε)(hd:d≤ reserve M B ε)
    (ht:theta≤ reserve M B ε)(ho:other≤ reserve M B ε)(he0:0≤ es)(hA:A≤ M)
    (hextra:extra≤50*reserve M B ε):
    CenteredMomentSuccessorPaidParameters.exceptional (amplification ε) df es d B theta+extra≤
      stageLoss M B ε (k+1) ∧
    CenteredMomentSuccessorPaidParameters.diagonal (amplification ε) d other es A+extra≤
      stageLoss M B ε (k+1):=by
  have hh:=one_time_losses M B κ ε hM hB hκ hε df es d theta other A hdf hes hd ht ho he0 hA
  exact ⟨one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.1 hextra,
    one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.2 hextra⟩

end CenteredMomentEnergyStageReserveSchedule

end

noncomputable section

namespace CenteredMomentEnergyStageMargins
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule

def physicalLoss (M B ε:ℝ)(k:ℕ):ℝ:=stageLoss M B ε (k+1)-2*reserve M B ε
def reflectedLoss (M B ε:ℝ)(k:ℕ):ℝ:=physicalLoss M B ε k+reserve M B ε

lemma physicalLoss_eq (M B ε:ℝ)(k:ℕ):
    physicalLoss M B ε k=stageLoss M B ε k+62*reserve M B ε:=by
  unfold physicalLoss stageLoss
  rw [loss_succ]
  ring
lemma reflected_then_zero (M B ε:ℝ)(k:ℕ):
    reflectedLoss M B ε k+reserve M B ε=stageLoss M B ε (k+1):=by
  unfold reflectedLoss physicalLoss
  ring
lemma margins (M B κ ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0< physicalLoss M B ε k ∧
    stageLoss M B ε k≤ physicalLoss M B ε k ∧
    reserve M B ε/4≤ physicalLoss M B ε k ∧
    physicalLoss M B ε k≤ reflectedLoss M B ε k ∧
    reflectedLoss M B ε k≤ stageLoss M B ε (k+1):=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have he:=stageLoss_pos M B κ ε hM hB hκ hε k
  have hp:=physicalLoss_eq M B ε k
  have hf:=reflected_then_zero M B ε k
  unfold reflectedLoss at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end CenteredMomentEnergyStageMargins

end

noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentEnergyFirstLiveAdmission
def readyBudget (A P : ℝ) : ℝ := 4*A + P + 10

lemma readyBudget_nonneg (A P : ℝ) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    0 ≤ readyBudget A P := by unfold readyBudget; linarith


end CenteredMomentEnergyFirstLiveAdmission
end

noncomputable section

namespace CenteredMomentEnergySourceCapSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyFirstLiveAdmission

lemma count_pos (M ε:ℝ):0< count M ε:=by
  unfold count CenteredMomentFirstSecondLossParameters.depth
  omega
lemma final_range_large (M B L ε:ℝ)(hM:0≤ M)(hB:0≤ B):
    20≤ range M B L (count M ε):=by
  have hh:=range_mono M B L hM hB (show 1≤ count M ε from count_pos M ε)
  have hm:1≤ max 1 L:=le_max_left _ _
  simp only [CenteredMomentEnergyWidthRanges.range,step] at hh
  linarith
lemma readyBudget_le_schedule (M B L ε A P:ℝ)(hM:0≤ M)(hB:0≤ B)
    (hA:A≤2*range M B L (count M ε)+M+1)(hP:P≤ B):
    readyBudget A P≤ finalSourceCap M B L ε:=by
  have hr:=final_range_large M B L ε hM hB
  unfold readyBudget finalSourceCap sourceCap
  linarith
lemma declared_capacity_le_schedule (M B L ε A:ℝ)(hM:0≤ M)(hB:0≤ B)
    (hA:A≤2*range M B L (count M ε)):
    max M A≤ finalSourceCap M B L ε:=by
  have hr:=final_range_large M B L ε hM hB
  apply max_le
  all_goals unfold finalSourceCap sourceCap;linarith

end CenteredMomentEnergySourceCapSchedule

end

noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges

def remaining (M ε:ℝ)(k:ℕ):ℕ:=count M ε-k
def lowerAt (a b M ε:ℝ)(k:ℕ):ℝ:=CenteredMomentEnergyProfiles.lower a b (remaining M ε k)
def lengthAt (M B L ε:ℝ)(k:ℕ):ℝ:=range M B L (remaining M ε k)

lemma lowerAt_pos (a b M ε:ℝ)(ha:0< a)(k:ℕ):0< lowerAt a b M ε k:=
  CenteredMomentEnergyProfiles.lower_pos a b ha _

lemma child_support (a b M ε:ℝ)(k:ℕ)(hk:k< count M ε):
    lowerAt a b M ε k=lowerAt a b M ε (k+1)/max 1 b:=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lowerAt,he,CenteredMomentEnergyProfiles.lower]

lemma child_length (M B L ε:ℝ)(k:ℕ)(hk:k< count M ε):
    lengthAt M B L ε k=step M B (lengthAt M B L ε (k+1)):=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lengthAt,he,CenteredMomentEnergyWidthRanges.range]


end CenteredMomentEnergyWidthInduction
end

noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule

def bandWidth (M B ε:ℝ)(k:ℕ):ℝ:=min M (width M B ε k)
lemma bandWidth_le (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤ M:=min_le_left _ _
lemma bandWidth_le_schedule (M B ε:ℝ)(k:ℕ):bandWidth M B ε k≤ width M B ε k:=min_le_right _ _
lemma bandWidth_nonneg (M B ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hε:0<ε)(k:ℕ):
    0≤ bandWidth M B ε k:=by
  have hr:0< reserve M B ε:=(bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.1
  have hs:0< amplification ε:=(bounds M B 0 ε hM hB (by norm_num) hε).1
  unfold bandWidth width
  positivity
lemma bandWidth_terminal (M B ε:ℝ)(hM:0≤ M)(hB:0≤ B)(hε:0<ε):
    bandWidth M B ε (count M ε)=M:=by
  have hh: M< width M B ε (count M ε):=
    (bounds M B 0 ε hM hB (by norm_num) hε).2.2.2.2.2.2.2.2.1
  exact min_eq_left hh.le
lemma actual_child_band (M B ε parent child:ℝ)(hε:0<ε)(k:ℕ)
    (hp:parent≤ bandWidth M B ε (k+1))(hc:child≤ parent-amplification ε/2):
    child≤ bandWidth M B ε k:=by
  have hs:0< amplification ε:=lt_min (by norm_num) (by positivity)
  apply le_min
  · have hh:=hp.trans (bandWidth_le M B ε (k+1));linarith
  · exact child_band M B ε parent child k (hp.trans (bandWidth_le_schedule M B ε (k+1))) hc


end CenteredMomentEnergyCappedWidthInduction
end

noncomputable section

namespace CenteredMomentEnergyCappedRequests
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergySourceCapSchedule

def requestLength (M B L:ℝ):ℝ:=max L (2*M+B+2)+1

lemma request_bounds (M B L:ℝ)(hM:0≤ M)(hB:0≤ B)(_hL:0≤ L):
    0≤ requestLength M B L ∧ L≤ requestLength M B L ∧ M≤ requestLength M B L:=by
  have hh:=le_max_left L (2*M+B+2)
  have hg:=le_max_right L (2*M+B+2)
  unfold requestLength
  constructor
  · linarith
  constructor <;> linarith

lemma actual_contours (M B L parent rho d:ℝ)(hM:0≤ M)(_hB:0≤ B)
    (hp:parent≤ M)(hr:rho≤ M)(hd:d≤1):
    max (max L (parent+B+2*d)+1) (parent+B+rho/100)≤ requestLength M B L:=by
  have hmax:max L (parent+B+2*d)≤ max L (2*M+B+2):=by
    apply max_le_max_left
    linarith
  have hh:=le_max_right L (2*M+B+2)
  unfold requestLength
  apply max_le <;> linarith

lemma doubled_request (M B L e:ℝ)(hM:0≤ M)(hB:0≤ B)(hL:0≤ L)(he:e≤1):
    2*requestLength M B L+e≤ step M B L:=by
  have hh:max L (2*M+B+2)≤ L+2*M+B+2:=by
    apply max_le <;> linarith
  unfold requestLength step
  linarith

lemma previous_admits (M B L ε parent e:ℝ)(hM:0≤ M)(hB:0≤ B)
    (hp:parent≤ M)(he:e≤1)(k:ℕ)(hk:k< count M ε):
    2*max (requestLength M B (lengthAt M B L ε (k+1))) parent+e≤ lengthAt M B L ε k:=by
  have hL:=range_nonneg M B L hM hB (remaining M ε (k+1))
  change 0≤ lengthAt M B L ε (k+1) at hL
  have hreq:=request_bounds M B (lengthAt M B L ε (k+1)) hM hB hL
  rw [max_eq_left (hp.trans hreq.2.2),child_length M B L ε k hk]
  exact doubled_request M B _ e hM hB hL he

lemma request_le_final (M B L ε:ℝ)(hM:0≤ M)(hB:0≤ B)(k:ℕ)(hk:k< count M ε):
    requestLength M B (lengthAt M B L ε (k+1))≤ range M B L (count M ε):=by
  have hh:=previous_admits M B L ε M 0 hM hB le_rfl (by norm_num) k hk
  have hl:=range_nonneg M B L hM hB (remaining M ε (k+1))
  have hr:0≤ requestLength M B (lengthAt M B L ε (k+1)):=
    (request_bounds M B _ hM hB hl).1
  have hprev:lengthAt M B L ε k≤ range M B L (count M ε):=
    range_mono M B L hM hB (Nat.sub_le _ _)
  have hmax:=le_max_left (requestLength M B (lengthAt M B L ε (k+1))) M
  linarith

lemma parent_drop (M B ε:ℝ)(hε:0<ε)(k:ℕ):
    bandWidth M B ε (k+1)-amplification ε/2≤ bandWidth M B ε k:=
  actual_child_band M B ε _ _ hε k le_rfl le_rfl

lemma band_positive (M B ε:ℝ)(hM:0< M)(hB:0≤ B)(hε:0<ε)(k:ℕ):
    0< bandWidth M B ε k:=by
  have hh:=bounds M B 0 ε hM.le hB (by norm_num) hε
  have hr:=hh.2.2.2.1
  have hs:=hh.1
  unfold bandWidth width
  exact lt_min hM (by positivity)

end CenteredMomentEnergyCappedRequests

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
