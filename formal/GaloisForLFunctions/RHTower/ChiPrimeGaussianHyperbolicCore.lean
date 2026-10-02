import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMain
import GaloisForLFunctions.RHTower.CompactGaussianPrimePacketCapacity
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount

/-!
# An actual hyperbolic prime core in the Gaussian cubic

Global prime mass, sparse-cell deletion and a source upper sieve bound construct
many noncontracting triples across disjoint gap scales. Their exact cubic phases
are coherent, their saddle windows equal one, and their actual Gaussian cutoff
factors have a fixed positive floor. The complete physical kernel error is small
per entry. Consequently the original physical core has mass at least c*N/log(N)^2.
The complete signed off-diagonal, including its complement, remains unresolved.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower PrimeCells

private def coreCell (S : Finset ℕ) (B h r : ℕ) : Finset ℕ :=
  S.filter (fun p => (p-B)/h = (r-B)/h)

private theorem coreCell_self {S : Finset ℕ} {B h r : ℕ} (hr : r ∈ S) :
    r ∈ coreCell S B h r := by simp [coreCell, hr]

private theorem coreCell_close {S : Finset ℕ} {B h p r : ℕ}
    (hh : 0 < h) (hpB : B ≤ p) (hrB : B ≤ r) (hp : p ∈ coreCell S B h r) :
    |(p:ℝ)-r| ≤ h := by
  have he := (Finset.mem_filter.mp hp).2
  have hp' := Nat.mod_add_div (p-B) h
  have hr' := Nat.mod_add_div (r-B) h
  have hpmod := Nat.mod_lt (p-B) hh
  have hrmod := Nat.mod_lt (r-B) hh
  rw [he] at hp'
  have hpr : p ≤ r+h := by omega
  have hrp : r ≤ p+h := by omega
  have hprR : (p:ℝ) ≤ r+h := by exact_mod_cast hpr
  have hrpR : (r:ℝ) ≤ p+h := by exact_mod_cast hrp
  rw [abs_le]
  constructor <;> linarith

private theorem sparse_fiber_mass_le (S J : Finset ℕ) (f : ℕ → ℕ)
    (hmap : ∀ r ∈ S, f r ∈ J) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((S.filter (fun r => ((S.filter (fun p => f p = f r)).card:ℝ) < ρ)).card:ℝ)
      ≤ (J.card:ℝ)*ρ := by
  classical
  let A := S.filter (fun r => ((S.filter (fun p => f p = f r)).card:ℝ) < ρ)
  have hmapA : (A:Set ℕ).MapsTo f J := fun r hr => hmap r (Finset.mem_filter.mp hr).1
  have he := Finset.card_eq_sum_card_fiberwise hmapA
  change (A.card:ℝ) ≤ _
  rw [he, Nat.cast_sum]
  calc
    _ ≤ ∑ _j ∈ J, ρ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hem : (A.filter (fun r => f r = j)) = ∅
      · simp only [hem, Finset.card_empty, Nat.cast_zero]
        exact hρ
      · obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hem
        obtain ⟨hrA, hrj⟩ := Finset.mem_filter.mp hr
        have hsmall := (Finset.mem_filter.mp hrA).2
        rw [hrj] at hsmall
        have hsub : A.filter (fun p => f p = j) ⊆ S.filter (fun p => f p = j) := by
          intro p hp
          obtain ⟨hpA, hpj⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpA).1, hpj⟩
        exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hsmall.le
    _ = _ := by simp

private theorem sparse_coreCell_mass_le {S : Finset ℕ} {N h : ℕ}
    (hN : 1 < (N:ℝ)) (hh : 0 < h) (hhN : h ≤ N)
    (hS : ∀ p ∈ S, N ≤ p ∧ p ≤ 2*N) :
    ((S.filter (fun r => ((coreCell S N h r).card:ℝ) <
      (h:ℝ)/(1024*Real.log N))).card:ℝ) ≤ 2*(N:ℝ)/(1024*Real.log N) := by
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos hN
  have hmap : ∀ p ∈ S, (p-N)/h ∈ Finset.range (N/h+1) := by
    intro p hp
    obtain ⟨_, hu⟩ := hS p hp
    apply Finset.mem_range.mpr
    have hd := Nat.div_le_div_right (show p-N ≤ N by omega) (c:=h)
    omega
  have hb := sparse_fiber_mass_le S (Finset.range (N/h+1)) (fun p => (p-N)/h)
    hmap (ρ := (h:ℝ)/(1024*Real.log N)) (by positivity)
  change ((S.filter (fun r => ((coreCell S N h r).card:ℝ) <
    (h:ℝ)/(1024*Real.log N))).card:ℝ) ≤ _ at hb
  apply hb.trans
  rw [Finset.card_range]
  have hdiv : ((N/h:ℕ):ℝ)*(h:ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N h
  have hhNR : (h:ℝ) ≤ N := by exact_mod_cast hhN
  push_cast
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 1024*Real.log (N:ℝ))
  nlinarith

private def coreAnchors (S : Finset ℕ) (N h L : ℕ) : Finset ℕ :=
  S.filter (fun r => (h:ℝ)/(1024*Real.log N) ≤ (coreCell S N h r).card ∧
    (L:ℝ)/(1024*Real.log N) ≤ (coreCell S N L r).card)

private theorem coreAnchors_mass {S : Finset ℕ} {N h L : ℕ}
    (hN : 1 < (N:ℝ)) (hh : 0 < h) (hL : 0 < L) (hhN : h ≤ N) (hLN : L ≤ N)
    (hS : ∀ p ∈ S, N ≤ p ∧ p ≤ 2*N)
    (hM : (N:ℝ)/(64*Real.log N) ≤ S.card) :
    (N:ℝ)/(128*Real.log N) ≤ (coreAnchors S N h L).card := by
  classical
  let A := S.filter (fun r => ((coreCell S N h r).card:ℝ) < (h:ℝ)/(1024*Real.log N))
  let B := S.filter (fun r => ((coreCell S N L r).card:ℝ) < (L:ℝ)/(1024*Real.log N))
  have hsub : S ⊆ coreAnchors S N h L ∪ A ∪ B := by
    intro r hr
    by_cases ha : (h:ℝ)/(1024*Real.log N) ≤ (coreCell S N h r).card
    · by_cases hb : (L:ℝ)/(1024*Real.log N) ≤ (coreCell S N L r).card
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, ha, hb⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, lt_of_not_ge hb⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, lt_of_not_ge ha⟩))
  have hc : S.card ≤ (coreAnchors S N h L).card + A.card + B.card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcR : (S.card:ℝ) ≤ (coreAnchors S N h L).card + (A.card:ℝ) + B.card := by exact_mod_cast hc
  have ha := sparse_coreCell_mass_le hN hh hhN hS
  have hb := sparse_coreCell_mass_le hN hL hLN hS
  change (A.card:ℝ) ≤ _ at ha
  change (B.card:ℝ) ≤ _ at hb
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos hN
  have he : (N:ℝ)/(64*Real.log N) - 2*(2*(N:ℝ)/(1024*Real.log N)) ≥
      (N:ℝ)/(128*Real.log N) := by
    field_simp
    nlinarith [Nat.cast_nonneg (α:=ℝ) N]
  linarith

private def coreFar (S : Finset ℕ) (N L K r : ℕ) : Finset ℕ :=
  (coreCell S N L r).filter (fun q : ℕ => (L:ℝ) < K*|(q:ℝ)-r|)

private def coreSlice (S : Finset ℕ) (N h L K : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  S.biUnion (fun r => (((coreCell S N h r).erase r) ×ˢ (coreFar S N L K r)).image
    (fun pq => (r,pq)))

private theorem card_coreSlice (S : Finset ℕ) (N h L K : ℕ) :
    (coreSlice S N h L K).card = ∑ r ∈ S,
      ((coreCell S N h r).erase r).card * (coreFar S N L K r).card := by
  classical
  unfold coreSlice
  have hdis : (S:Set ℕ).PairwiseDisjoint
      (fun r => (((coreCell S N h r).erase r) ×ˢ (coreFar S N L K r)).image (fun pq => (r,pq))) := by
    intro r _ s _ hrs
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨pq, _, hpq⟩ := Finset.mem_image.mp hz
    obtain ⟨ab, _, hab⟩ := Finset.mem_image.mp hz'
    exact hrs (congrArg Prod.fst (hpq.trans hab.symm))
  rw [Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.card_image_of_injective _ (fun _ _ hh => (Prod.mk.inj hh).2), Finset.card_product]

private theorem coreFar_mass {S : Finset ℕ} {N L K r : ℕ}
    (hN : 1 < (N:ℝ))
    (hr : (L:ℝ)/(1024*Real.log N) ≤ (coreCell S N L r).card)
    (hnear : ((S.filter (fun q : ℕ => K*|(q:ℝ)-r| ≤ L)).card:ℝ) ≤ (L:ℝ)/(2048*Real.log N)) :
    (L:ℝ)/(2048*Real.log N) ≤ (coreFar S N L K r).card := by
  classical
  have he := Finset.card_filter_add_card_filter_not (s := coreCell S N L r)
    (fun q : ℕ => (L:ℝ) < K*|(q:ℝ)-r|)
  have hsub : (coreCell S N L r).filter (fun q : ℕ => ¬ (L:ℝ) < K*|(q:ℝ)-r|) ⊆
      S.filter (fun q : ℕ => K*|(q:ℝ)-r| ≤ L) := by
    intro q hq
    obtain ⟨hqcell, hqgap⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqcell).1, le_of_not_gt hqgap⟩
  have hc := (Nat.cast_le (α:=ℝ)).mpr (Finset.card_le_card hsub)
  have heR : ((coreFar S N L K r).card:ℝ) +
      ((coreCell S N L r).filter (fun q : ℕ => ¬ (L:ℝ) < K*|(q:ℝ)-r|)).card =
      (coreCell S N L r).card := by
    dsimp only [coreFar]
    exact_mod_cast he
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos hN
  have heq : (L:ℝ)/(1024*Real.log N) = 2*((L:ℝ)/(2048*Real.log N)) := by ring
  rw [heq] at hr
  linarith

private theorem coreSlice_mass {S : Finset ℕ} {N h L K : ℕ}
    (hN : 1 < (N:ℝ)) (hh : 0 < h) (hL : 0 < L) (hhN : h ≤ N) (hLN : L ≤ N)
    (hS : ∀ p ∈ S, N ≤ p ∧ p ≤ 2*N)
    (hM : (N:ℝ)/(64*Real.log N) ≤ S.card)
    (hhlarge : 2048*Real.log N ≤ (h:ℝ))
    (hnear : ∀ r ∈ S, ((S.filter (fun q : ℕ => K*|(q:ℝ)-r| ≤ L)).card:ℝ) ≤
      (L:ℝ)/(2048*Real.log N)) :
    (N:ℝ)*h*L/(536870912*(Real.log N)^3) ≤ (coreSlice S N h L K).card := by
  classical
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos hN
  have hG := coreAnchors_mass hN hh hL hhN hLN hS hM
  have hrow (r : ℕ) (hr : r ∈ coreAnchors S N h L) :
      (h:ℝ)/(2048*Real.log N) * ((L:ℝ)/(2048*Real.log N)) ≤
        (((coreCell S N h r).erase r).card:ℝ) * (coreFar S N L K r).card := by
    obtain ⟨hrS, hrh, hrL⟩ := Finset.mem_filter.mp hr
    have hq := coreFar_mass hN hrL (hnear r hrS)
    have hep := Finset.card_erase_add_one (coreCell_self (B:=N) (h:=h) hrS)
    have hepR : (((coreCell S N h r).erase r).card:ℝ)+1 = (coreCell S N h r).card := by exact_mod_cast hep
    have hhl : 2 ≤ (h:ℝ)/(1024*Real.log N) := by
      apply (le_div_iff₀ (by positivity : 0<1024*Real.log (N:ℝ))).mpr
      nlinarith only [hhlarge]
    have heq : (h:ℝ)/(1024*Real.log N) = 2*((h:ℝ)/(2048*Real.log N)) := by ring
    have hp : (h:ℝ)/(2048*Real.log N) ≤ ((coreCell S N h r).erase r).card := by
      rw [heq] at hrh hhl
      linarith
    exact mul_le_mul hp hq (by positivity) (by positivity)
  rw [card_coreSlice, Nat.cast_sum]
  calc
    _ = ((N:ℝ)/(128*Real.log N)) * ((h:ℝ)/(2048*Real.log N) * ((L:ℝ)/(2048*Real.log N))) := by field_simp; ring
    _ ≤ ((coreAnchors S N h L).card:ℝ) *
        ((h:ℝ)/(2048*Real.log N) * ((L:ℝ)/(2048*Real.log N))) :=
      mul_le_mul_of_nonneg_right hG (by positivity)
    _ = ∑ _r ∈ coreAnchors S N h L,
        ((h:ℝ)/(2048*Real.log N) * ((L:ℝ)/(2048*Real.log N))) := by simp
    _ ≤ ∑ r ∈ coreAnchors S N h L,
        (((coreCell S N h r).erase r).card:ℝ) * (coreFar S N L K r).card :=
      Finset.sum_le_sum hrow
    _ ≤ _ := by
      push_cast
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)

private def corePrimeBand (N : ℕ) : Finset ℕ :=
  windowPrimes (3*(N:ℝ)/2) (25*(N:ℝ)/16)

private theorem corePrimeBand_mem {N p : ℕ} (hN : 0 < N) (hp : p ∈ corePrimeBand N) :
    p.Prime ∧ 3*(N:ℝ)/2 < p ∧ (p:ℝ) ≤ 25*(N:ℝ)/16 := by
  exact (mem_windowPrimes (by positivity) (by positivity)).mp hp

private theorem corePrimeBand_frame {N p : ℕ} (hN : 0 < N) (hp : p ∈ corePrimeBand N) :
    N ≤ p ∧ p ≤ 2*N := by
  obtain ⟨_, hl, hu⟩ := corePrimeBand_mem hN hp
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  constructor
  · exact_mod_cast (show (N:ℝ) ≤ p by linarith)
  · exact_mod_cast (show (p:ℝ) ≤ 2*N by linarith)

private theorem exists_corePrimeBand_mass :
    ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ N : ℕ, R₀ ≤ (N:ℝ) →
      (N:ℝ)/(64*Real.log N) ≤ (corePrimeBand N).card := by
  obtain ⟨R, hR, hcount⟩ := exists_card_windowPrimes_div_ge 1 (ε:=1/2) (by norm_num)
  refine ⟨max R (Real.exp 16), ?_, ?_⟩
  · have hh : (2:ℝ) ≤ R := by linarith
    exact hh.trans (le_max_left _ _)
  intro N hN
  have hNR : R ≤ (N:ℝ) := (le_max_left _ _).trans hN
  have hN3 : (3:ℝ) ≤ N := hR.trans hNR
  have hN0 : (0:ℝ) < N := by linarith
  have hlog : 16 ≤ Real.log (N:ℝ) := by
    rw [← Real.log_exp 16]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hN)
  have hlog2 : 0 < Real.log (2*(N:ℝ)) := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log (N:ℝ) := by linarith
  have hlogmono : Real.log (N:ℝ) ≤ Real.log (2*(N:ℝ)) :=
    Real.log_le_log hN0 (by linarith)
  have hh := hcount (2*(N:ℝ)) (by linarith) 2 (by norm_num) (by norm_num)
    (3*(N:ℝ)) (25*(N:ℝ)/8) (by linarith) (by linarith) (by linarith)
    (by rw [Real.rpow_one]; apply (div_le_iff₀ hlog2).mpr; nlinarith)
  have hw : windowPrimes (3*(N:ℝ)/2) ((25*(N:ℝ)/8)/2) = corePrimeBand N := by
    unfold corePrimeBand
    congr 1
    ring
  rw [hw] at hh
  have hlogs : Real.log (2*(N:ℝ)) ≤ 2*Real.log (N:ℝ) := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hN0.ne']
    have h2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by linarith : (2:ℝ) ≤ N)
    linarith
  calc
    _ ≤ (N:ℝ)/(32*Real.log (2*(N:ℝ))) :=
      div_le_div_of_nonneg_left hN0.le (by positivity) (by linarith)
    _ = (1-1/2)*(25*(N:ℝ)/8-3*N)/(2*Real.log (2*(N:ℝ))) := by ring
    _ ≤ _ := hh

private def coreBase : ℕ := 10000000
/-- Cofinal conductors for the disjoint hyperbolic prime-gap scales. -/
def primeGaussianHyperbolicConductor (m : ℕ) : ℕ := coreBase^(4*m)
private def coreFine (m j : ℕ) : ℕ := coreBase^(2*m-j-1)
private def coreCoarse (m j : ℕ) : ℕ := coreBase^(2*m+j)

private theorem coreBase_pos : 0 < coreBase := by norm_num [coreBase]
private theorem coreBase_real_pos : (0:ℝ) < coreBase := by exact_mod_cast coreBase_pos
private theorem coreConductor_pos (m : ℕ) : 0 < primeGaussianHyperbolicConductor m := by
  exact pow_pos coreBase_pos _
private theorem core_scale {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) :
    0 < coreFine m j ∧ 0 < coreCoarse m j ∧ coreFine m j ≤ primeGaussianHyperbolicConductor m ∧
      coreCoarse m j ≤ primeGaussianHyperbolicConductor m ∧
      coreFine m j*coreCoarse m j*coreBase = primeGaussianHyperbolicConductor m ∧
      coreBase^m ≤ coreFine m j ∧ coreBase^m*coreBase ≤ coreCoarse m j := by
  dsimp [coreFine, coreCoarse, primeGaussianHyperbolicConductor]
  refine ⟨pow_pos coreBase_pos _, pow_pos coreBase_pos _,
    Nat.pow_le_pow_right coreBase_pos (by omega),
    Nat.pow_le_pow_right coreBase_pos (by omega), ?_,
    Nat.pow_le_pow_right coreBase_pos (by omega), ?_⟩
  · rw [← pow_add, ← pow_succ]
    congr 1
    omega
  · rw [← pow_succ]
    exact Nat.pow_le_pow_right coreBase_pos (by omega)

private theorem core_log_conductor (m : ℕ) :
    Real.log (primeGaussianHyperbolicConductor m:ℝ) = 4*(m:ℝ)*Real.log (coreBase:ℝ) := by
  simp only [primeGaussianHyperbolicConductor, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]

/-- The source conductors escape to infinity. -/
theorem tendsto_primeGaussianHyperbolicConductor :
    Tendsto (fun m : ℕ => (primeGaussianHyperbolicConductor m:ℝ)) atTop atTop := by
  have ht := tendsto_pow_atTop_atTop_of_one_lt (by norm_num [coreBase] : (1:ℝ) < coreBase)
  have ht4 := (tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0)).comp ht
  convert ht4 using 1
  funext m
  simp only [primeGaussianHyperbolicConductor, Nat.cast_pow, Function.comp_apply, ← pow_mul]
  congr 1
  omega

private theorem eventually_core_fine_large :
    ∀ᶠ m : ℕ in atTop, ∀ j < m,
      2048*Real.log (primeGaussianHyperbolicConductor m:ℝ) ≤ (coreFine m j:ℝ) := by
  have hs : ∀ᶠ x : ℝ in atTop, 8192*Real.log x ≤ x := by
    have hh := Real.isLittleO_log_id_atTop.def (c:=1/8192) (by norm_num)
    filter_upwards [hh, eventually_ge_atTop (1:ℝ)] with x hx hx1
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1), id,
      abs_of_nonneg (by linarith : 0 ≤ x)] at hx
    linarith
  have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num [coreBase] : (1:ℝ) < coreBase)
  filter_upwards [hp.eventually hs, eventually_ge_atTop (1:ℕ)] with m hm hm1
  intro j hj
  have hscale := core_scale hm1 hj
  have hlo : ((coreBase:ℝ)^m) ≤ coreFine m j := by exact_mod_cast hscale.2.2.2.2.2.1
  rw [Real.log_pow] at hm
  rw [core_log_conductor]
  nlinarith only [hm, hlo]

private theorem core_near_prime_count {m j r : ℕ} (hm : 1 ≤ m) (hj : j < m)
    (hr : r ∈ corePrimeBand (primeGaussianHyperbolicConductor m)) :
    (((corePrimeBand (primeGaussianHyperbolicConductor m)).filter
      (fun q : ℕ => (coreBase:ℝ)*|(q:ℝ)-r| ≤ coreCoarse m j)).card:ℝ) ≤
      (coreCoarse m j:ℝ)/(2048*Real.log (primeGaussianHyperbolicConductor m)) := by
  let N := primeGaussianHyperbolicConductor m
  let L := coreCoarse m j
  let D : ℝ := (L:ℝ)/(coreBase:ℝ)
  have hscale := core_scale hm hj
  have hN0 : (0:ℝ) < N := by exact_mod_cast coreConductor_pos m
  have hL0 : (0:ℝ) < L := by exact_mod_cast hscale.2.1
  have hD0 : 0 < D := div_pos hL0 coreBase_real_pos
  have hLN : (L:ℝ) ≤ N := by exact_mod_cast hscale.2.2.2.1
  have hDle : D ≤ (N:ℝ)/2 := by
    dsimp [D]
    have hK : (2:ℝ) ≤ coreBase := by norm_num [coreBase]
    calc
      _ ≤ (N:ℝ)/(coreBase:ℝ) := div_le_div_of_nonneg_right hLN coreBase_real_pos.le
      _ ≤ _ := div_le_div_of_nonneg_left hN0.le (by norm_num) hK
  have hNr : (N:ℝ) ≤ r := by exact_mod_cast (corePrimeBand_frame (coreConductor_pos m) hr).1
  have ha : 0 < (r:ℝ)-D := by linarith
  have hX : ((coreBase:ℝ)^m) ≤ D := by
    apply (le_div_iff₀ coreBase_real_pos).mpr
    exact_mod_cast hscale.2.2.2.2.2.2
  have hX1 : (1:ℝ) ≤ (coreBase:ℝ)^m := one_le_pow₀ (by norm_num [coreBase])
  have hH : 1 < 2*D := by linarith
  have hlogN : 0 < Real.log (N:ℝ) := by
    dsimp [N]
    rw [core_log_conductor]
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have hklog : 0 < Real.log (coreBase:ℝ) := Real.log_pos (by norm_num [coreBase])
    positivity
  have hlogH : Real.log (N:ℝ)/4 ≤ Real.log (2*D) := by
    have hxlog := Real.log_le_log (by positivity : (0:ℝ) < (coreBase:ℝ)^m)
      (show (coreBase:ℝ)^m ≤ 2*D by linarith)
    rw [Real.log_pow] at hxlog
    dsimp [N]
    rw [core_log_conductor]
    linarith
  let A := (corePrimeBand N).filter (fun q : ℕ => (coreBase:ℝ)*|(q:ℝ)-r| ≤ L)
  have hsub : A ⊆ (Finset.Icc ⌈(r:ℝ)-D⌉₊ ⌊((r:ℝ)-D)+2*D⌋₊).filter Nat.Prime := by
    intro q hq
    obtain ⟨hqS, hqgap⟩ := Finset.mem_filter.mp hq
    have hqp := (corePrimeBand_mem (coreConductor_pos m) hqS).1
    have hgap : |(q:ℝ)-r| ≤ D := (le_div_iff₀ coreBase_real_pos).mpr (by simpa [mul_comm] using hqgap)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hgap
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.ceil_le.mpr (by linarith), Nat.le_floor (by linarith)⟩, hqp⟩
  have hc : (A.card:ℝ) ≤ (BrunTitchmarsh.primesBetween ((r:ℝ)-D) (((r:ℝ)-D)+2*D):ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbt := bagPacket_primesBetween_le_div_log ha hH
  change (A.card:ℝ) ≤ _
  have hlogH0 : 0 < Real.log (2*D) := Real.log_pos hH
  calc
    _ ≤ 292*(2*D)/Real.log (2*D) := hc.trans hbt
    _ ≤ 292*(2*D)/(Real.log (N:ℝ)/4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlogH
    _ = (2336/(coreBase:ℝ))*((L:ℝ)/Real.log (N:ℝ)) := by dsimp [D]; ring
    _ ≤ (1/2048)*((L:ℝ)/Real.log (N:ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num [coreBase]) (by positivity)
    _ = _ := by ring

private theorem mem_coreSlice {S : Finset ℕ} {N h L K r p q : ℕ} :
    (r,p,q)  ∈  coreSlice S N h L K ↔
      r  ∈  S  ∧  p  ∈  (coreCell S N h r).erase r  ∧  q  ∈  coreFar S N L K r := by
  classical
  constructor
  · intro ht
    obtain ⟨s, hs, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨⟨a,b⟩, hab, he⟩ := Finset.mem_image.mp ht
    obtain ⟨rfl, he'⟩ := Prod.mk.inj he
    cases he'
    exact ⟨hs, (Finset.mem_product.mp hab).1, (Finset.mem_product.mp hab).2⟩
  · rintro ⟨hr,hp,hq⟩
    exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_image.mpr
      ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,rfl⟩⟩

private theorem coreSlice_geometry {S : Finset ℕ} {N h L K r p q : ℕ}
    (hh : 0<h) (hL : 0<L) (hS : ∀ x  ∈  S, N ≤ x  ∧  x ≤ 2*N)
    (ht : (r,p,q)  ∈  coreSlice S N h L K) :
    r ∈ S  ∧  p ∈ S  ∧  q ∈ S  ∧  p ≠ r  ∧  q ≠ r  ∧  |(p:ℝ)-r| ≤ h  ∧ 
      |(q:ℝ)-r| ≤ L  ∧  (L:ℝ)<K*|(q:ℝ)-r| := by
  obtain ⟨hr,hp,hq⟩ := mem_coreSlice.mp ht
  obtain ⟨hpr,hpc⟩ := Finset.mem_erase.mp hp
  obtain ⟨hqc,hgap⟩ := Finset.mem_filter.mp hq
  have hpS := (Finset.mem_filter.mp hpc).1
  have hqS := (Finset.mem_filter.mp hqc).1
  refine ⟨hr,hpS,hqS,hpr,?_,
    coreCell_close hh (hS p hpS).1 (hS r hr).1 hpc,
    coreCell_close hL (hS q hqS).1 (hS r hr).1 hqc,hgap⟩
  intro he
  subst q
  simp only [sub_self, abs_zero, mul_zero] at hgap
  exact (Nat.cast_nonneg L).not_gt hgap

private theorem coreCoarse_separated {m i j : ℕ} (hij : i<j) :
    coreCoarse m i*coreBase  ≤  coreCoarse m j := by
  dsimp [coreCoarse]
  rw [← pow_succ]
  exact Nat.pow_le_pow_right coreBase_pos (by omega)

/-- Actual prime triples `(r,p,q)`, grouped into disjoint coarse-gap annuli.
All three primes lie in `(3N/2,25N/16]`; fine-cell partners exclude the anchor. -/
def primeGaussianHyperbolicCore (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range m).biUnion (fun j => coreSlice (corePrimeBand (primeGaussianHyperbolicConductor m))
    (primeGaussianHyperbolicConductor m) (coreFine m j) (coreCoarse m j) coreBase)

private theorem coreSlice_pairwiseDisjoint {m : ℕ} (hm : 1 ≤ m) :
    (↑(Finset.range m):Set ℕ).PairwiseDisjoint (fun j =>
      coreSlice (corePrimeBand (primeGaussianHyperbolicConductor m)) (primeGaussianHyperbolicConductor m)
        (coreFine m j) (coreCoarse m j) coreBase) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  rintro ⟨r,p,q⟩ ht hu
  have him := Finset.mem_range.mp hi
  have hjm := Finset.mem_range.mp hj
  have hsi := core_scale hm him
  have hsj := core_scale hm hjm
  have hs : ∀ x ∈ corePrimeBand (primeGaussianHyperbolicConductor m), primeGaussianHyperbolicConductor m ≤ x ∧ x ≤ 2*primeGaussianHyperbolicConductor m :=
    fun x hx => corePrimeBand_frame (coreConductor_pos m) hx
  have hg := coreSlice_geometry hsi.1 hsi.2.1 hs ht
  have hh := coreSlice_geometry hsj.1 hsj.2.1 hs hu
  rcases lt_or_gt_of_ne hij with hij|hji
  · have he : (coreCoarse m i:ℝ)*coreBase  ≤  coreCoarse m j := by
      exact_mod_cast coreCoarse_separated hij
    have hb := mul_le_mul_of_nonneg_left hg.2.2.2.2.2.2.1 coreBase_real_pos.le
    nlinarith only [hb,he,hh.2.2.2.2.2.2.2]
  · have he : (coreCoarse m j:ℝ)*coreBase  ≤  coreCoarse m i := by
      exact_mod_cast coreCoarse_separated hji
    have hb := mul_le_mul_of_nonneg_left hh.2.2.2.2.2.2.1 coreBase_real_pos.le
    nlinarith only [hb,he,hg.2.2.2.2.2.2.2]

/-- Many disjoint gap scales supply a logarithmic factor beyond a single coherent box.
All prime counts and near-partner exclusions are derived from source PNT and sieve theorems. -/
theorem exists_primeGaussianHyperbolicCore_card :
    ∃ c : ℝ, 0<c  ∧  ∀ᶠ m : ℕ in atTop,
      c*(primeGaussianHyperbolicConductor m:ℝ)^2/(Real.log (primeGaussianHyperbolicConductor m))^2  ≤  (primeGaussianHyperbolicCore m).card := by
  let c : ℝ := 1/(2147483648*(coreBase:ℝ)*Real.log (coreBase:ℝ))
  have hklog : 0 < Real.log (coreBase:ℝ) := Real.log_pos (by norm_num [coreBase])
  have hc : 0<c := by
    dsimp [c]
    exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) coreBase_real_pos) hklog)
  obtain ⟨R₀,hR₀,hM⟩ := exists_corePrimeBand_mass
  refine ⟨c,hc,?_⟩
  filter_upwards [tendsto_primeGaussianHyperbolicConductor.eventually_ge_atTop R₀,
    eventually_core_fine_large,eventually_ge_atTop (1:ℕ)] with m hmR hml hm
  have hN : 1 < (primeGaussianHyperbolicConductor m:ℝ) := by linarith
  have hlog : 0 < Real.log (primeGaussianHyperbolicConductor m:ℝ) := Real.log_pos hN
  have hrow (j : ℕ) (hj : j  ∈  Finset.range m) :
      (primeGaussianHyperbolicConductor m:ℝ)^2/(536870912*(coreBase:ℝ)*(Real.log (primeGaussianHyperbolicConductor m))^3)  ≤ 
      (coreSlice (corePrimeBand (primeGaussianHyperbolicConductor m)) (primeGaussianHyperbolicConductor m)
        (coreFine m j) (coreCoarse m j) coreBase).card := by
    have hjm := Finset.mem_range.mp hj
    have hsc := core_scale hm hjm
    have hh := coreSlice_mass hN hsc.1 hsc.2.1 hsc.2.2.1 hsc.2.2.2.1
      (fun x hx => corePrimeBand_frame (coreConductor_pos m) hx) (hM _ hmR)
      (hml j hjm) (fun r hr => core_near_prime_count hm hjm hr)
    have hk0 := coreBase_real_pos
    have hp : (coreFine m j:ℝ)*coreCoarse m j*coreBase = primeGaussianHyperbolicConductor m := by
      exact_mod_cast hsc.2.2.2.2.1
    have he : (primeGaussianHyperbolicConductor m:ℝ)^2/(536870912*(coreBase:ℝ)*(Real.log (primeGaussianHyperbolicConductor m))^3) =
        (primeGaussianHyperbolicConductor m:ℝ)*coreFine m j*coreCoarse m j/(536870912*(Real.log (primeGaussianHyperbolicConductor m))^3) := by
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      linear_combination -(536870912*(Real.log (primeGaussianHyperbolicConductor m))^3*(primeGaussianHyperbolicConductor m:ℝ))*hp
    rw [he]
    exact hh
  rw [primeGaussianHyperbolicCore, Finset.card_biUnion (coreSlice_pairwiseDisjoint hm), Nat.cast_sum]
  calc
    _ = (m:ℝ)*((primeGaussianHyperbolicConductor m:ℝ)^2/
        (536870912*(coreBase:ℝ)*(Real.log (primeGaussianHyperbolicConductor m))^3)) := by
      dsimp [c]
      have hmR : (m:ℝ)  ≠  0 := by exact_mod_cast (show m ≠ 0 by omega)
      rw [core_log_conductor]
      field_simp
      ring
    _ = ∑ _j  ∈  Finset.range m, (primeGaussianHyperbolicConductor m:ℝ)^2/
        (536870912*(coreBase:ℝ)*(Real.log (primeGaussianHyperbolicConductor m))^3) := by simp
    _  ≤  _ := Finset.sum_le_sum hrow

private theorem coreFamily_geometry {m r p q : ℕ} (ht : (r,p,q)  ∈  primeGaussianHyperbolicCore m) :
    r ∈ corePrimeBand (primeGaussianHyperbolicConductor m)  ∧  p ∈ corePrimeBand (primeGaussianHyperbolicConductor m)  ∧ 
    q ∈ corePrimeBand (primeGaussianHyperbolicConductor m)  ∧  p ≠ r  ∧  q ≠ r  ∧ 
    |(p:ℝ)-r| * |(q:ℝ)-r|  ≤  (primeGaussianHyperbolicConductor m:ℝ)/(coreBase:ℝ) := by
  obtain ⟨j,hj,ht⟩ := Finset.mem_biUnion.mp ht
  have hjm := Finset.mem_range.mp hj
  have hm : 1 ≤ m := by omega
  have hsc := core_scale hm hjm
  have hg := coreSlice_geometry hsc.1 hsc.2.1
    (fun x hx => corePrimeBand_frame (coreConductor_pos m) hx) ht
  refine ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,?_⟩
  have hb := mul_le_mul hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 (abs_nonneg _) (by positivity)
  have hp : (coreFine m j:ℝ)*coreCoarse m j*coreBase = primeGaussianHyperbolicConductor m := by
    exact_mod_cast hsc.2.2.2.2.1
  apply hb.trans
  apply (le_div_iff₀ coreBase_real_pos).mpr
  exact hp.le

private theorem corePrimeBand_full {N p : ℕ} (hN : 0 < N)
    (hp : p ∈ corePrimeBand N) : p ∈ primeProfileBand (N:ℝ) := by
  obtain ⟨hp,hl,hu⟩ := corePrimeBand_mem hN hp
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
  · exact (Nat.floor_lt hN0.le).mpr (by linarith)
  · exact Nat.le_floor (by linarith)

private theorem core_window {N p q r : ℕ} (hN : 0 < N)
    (hp : p ∈ corePrimeBand N) (hq : q ∈ corePrimeBand N)
    (hr : r ∈ corePrimeBand N) :
    bagPhysicalHeightWindow ((p:ℝ)*q/((r:ℝ)*N)) = 1 := by
  obtain ⟨_,hpl,hpu⟩ := corePrimeBand_mem hN hp
  obtain ⟨_,hql,hqu⟩ := corePrimeBand_mem hN hq
  obtain ⟨_,hrl,hru⟩ := corePrimeBand_mem hN hr
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hp0 : (0:ℝ) < p := by linarith
  have hq0 : (0:ℝ) < q := by linarith
  have hr0 : (0:ℝ) < r := by linarith
  have hlo := mul_le_mul hpl.le hql.le (by positivity : 0 ≤ 3*(N:ℝ)/2) hp0.le
  have hhi := mul_le_mul hpu hqu hq0.le (by positivity : 0 ≤ 25*(N:ℝ)/16)
  have hrlN := mul_le_mul_of_nonneg_right hrl.le hN0.le
  have hruN := mul_le_mul_of_nonneg_right hru hN0.le
  have hl : (5:ℝ)/4 ≤ (p:ℝ)*q/((r:ℝ)*N) := by
    apply (le_div_iff₀ (mul_pos hr0 hN0)).mpr
    nlinarith only [hlo,hruN,sq_nonneg (N:ℝ)]
  have hu : (p:ℝ)*q/((r:ℝ)*N) ≤ (7:ℝ)/4 := by
    apply (div_le_iff₀ (mul_pos hr0 hN0)).mpr
    nlinarith only [hhi,hrlN,sq_nonneg (N:ℝ)]
  apply bagPhysicalHeightWindow.one_of_mem_closedBall
  change dist ((p:ℝ)*q/((r:ℝ)*N)) (3/2) ≤ 1/4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

private def coreCutoffFloor : ℝ := (smoothAFECutoff 2).re
private theorem coreCutoffFloor_pos : 0 < coreCutoffFloor :=
  smoothAFECutoff_re_pos (by norm_num)

private theorem core_cutoff {N p : ℕ} (hN : 0 < N) (hp : p ∈ corePrimeBand N) :
    smoothAFECutoff ((p:ℝ)/N) = ((smoothAFECutoff ((p:ℝ)/N)).re:ℂ) ∧
      coreCutoffFloor ≤ (smoothAFECutoff ((p:ℝ)/N)).re := by
  obtain ⟨_,hl,hu⟩ := corePrimeBand_mem hN hp
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < (p:ℝ)/N := div_pos (by linarith) hN0
  constructor
  · apply Complex.ext <;> simp [smoothAFECutoff_im_eq_zero hx]
  · exact smoothAFECutoff_re_antitoneOn hx (by norm_num)
      ((div_le_iff₀ hN0).mpr (by linarith))

private theorem core_phase_re {m r p q : ℕ} (ht : (r,p,q) ∈ primeGaussianHyperbolicCore m) :
    1/2 ≤ (bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))).re := by
  have hg := coreFamily_geometry ht
  obtain ⟨_,hrl,hru⟩ := corePrimeBand_mem (coreConductor_pos m) hg.1
  have hN0 : (0:ℝ) < primeGaussianHyperbolicConductor m := by exact_mod_cast coreConductor_pos m
  have hr0 : (0:ℝ) < r := by linarith
  have hrNat : 0 < r := by exact_mod_cast hr0
  rw [primeGaussianCubic_phase_recenter p q hrNat]
  let θ : ℝ := 2*Real.pi*(((p:ℝ)-r)*((q:ℝ)-r)/r)
  have hθ : |θ| ≤ 1/2 := by
    have hk0 := coreBase_real_pos
    have hπ : 2*Real.pi/(coreBase:ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ coreBase_real_pos).mpr
      norm_num only [coreBase, Nat.cast_ofNat]
      linarith [Real.pi_lt_four]
    calc
      |θ| = 2*Real.pi/r*(|(p:ℝ)-r| * |(q:ℝ)-r|) := by
        dsimp [θ]
        simp only [abs_mul, abs_div, abs_of_pos hr0, abs_of_pos Real.pi_pos,
          abs_of_pos (by norm_num : (0:ℝ) < 2)]
        ring
      _ ≤ 2*Real.pi/r*((primeGaussianHyperbolicConductor m:ℝ)/coreBase) :=
        mul_le_mul_of_nonneg_left hg.2.2.2.2.2 (by positivity)
      _ ≤ 2*Real.pi/coreBase := by
        apply (le_of_mul_le_mul_right ?_ (mul_pos hr0 coreBase_real_pos))
        field_simp
        nlinarith only [hrl,Real.pi_pos,hN0]
      _ ≤ 1/2 := hπ
  have hb := (norm_bourgainOscillation_sub_le θ 0).trans (by simpa only [sub_zero] using hθ)
  simp only [bourgainOscillation, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at hb
  have hre := (Complex.abs_re_le_norm (bourgainOscillation θ-1)).trans hb
  rw [abs_le] at hre
  simp only [Complex.sub_re, Complex.one_re] at hre
  change (1:ℝ)/2 ≤ (bourgainOscillation θ).re
  linarith [hre.1]

private theorem core_main_entry_lower {m r p q : ℕ} (ht : (r,p,q) ∈ primeGaussianHyperbolicCore m) :
    coreCutoffFloor^3/(2*(primeGaussianHyperbolicConductor m:ℝ)) ≤
      (primeGaussianCubicMainEntry (primeGaussianHyperbolicConductor m) p q r).re := by
  have hg := coreFamily_geometry ht
  have hv := coreCutoffFloor_pos
  have hN := coreConductor_pos m
  have hN0 : (0:ℝ) < primeGaussianHyperbolicConductor m := by exact_mod_cast hN
  obtain ⟨hpr,hpv⟩ := core_cutoff hN hg.2.1
  obtain ⟨hqr,hqv⟩ := core_cutoff hN hg.2.2.1
  obtain ⟨hrr,hrv⟩ := core_cutoff hN hg.1
  have hW := core_window hN hg.2.1 hg.2.2.1 hg.1
  have hphase := core_phase_re ht
  obtain ⟨_,hrl,hru⟩ := corePrimeBand_mem hN hg.1
  have hr0 : (0:ℝ) < r := by linarith
  let a := (smoothAFECutoff ((p:ℝ)/primeGaussianHyperbolicConductor m)).re
  let b := (smoothAFECutoff ((q:ℝ)/primeGaussianHyperbolicConductor m)).re
  let c := (smoothAFECutoff ((r:ℝ)/primeGaussianHyperbolicConductor m)).re
  have ha : 0 ≤ a := coreCutoffFloor_pos.le.trans hpv
  have hb : 0 ≤ b := coreCutoffFloor_pos.le.trans hqv
  have hc : 0 ≤ c := coreCutoffFloor_pos.le.trans hrv
  have habc : coreCutoffFloor^3 ≤ a*b*c := by
    have hab := mul_le_mul hpv hqv coreCutoffFloor_pos.le ha
    have hh := mul_le_mul hab hrv coreCutoffFloor_pos.le (mul_nonneg ha hb)
    simpa only [pow_succ, pow_zero, one_mul] using hh
  have hf : 1/(primeGaussianHyperbolicConductor m:ℝ) ≤ 2*Real.pi/r := by
    apply (div_le_div_iff₀ hN0 hr0).mpr
    nlinarith [Real.pi_gt_three]
  have hamp : coreCutoffFloor^3/(primeGaussianHyperbolicConductor m:ℝ) ≤ 2*Real.pi/r*(a*b*c) := by
    simpa only [one_mul, div_mul_eq_mul_div] using
      mul_le_mul hf habc (by positivity : 0 ≤ coreCutoffFloor^3) (by positivity : 0 ≤ 2*Real.pi/r)
  have he : (primeGaussianCubicMainEntry (primeGaussianHyperbolicConductor m) p q r).re =
      (2*Real.pi/r*(a*b*c))*(bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))).re := by
    unfold primeGaussianCubicMainEntry
    rw [hpr,hqr,hrr,hW]
    simp only [Complex.conj_ofReal, Complex.ofReal_one, mul_one]
    have hfac : (2*Real.pi:ℂ)*(a:ℂ)*(b:ℂ)*(c:ℂ)/(r:ℂ) =
        ((2*Real.pi/r*(a*b*c):ℝ):ℂ) := by push_cast; ring
    change ((2*Real.pi:ℂ)*(a:ℂ)*(b:ℂ)*(c:ℂ)/(r:ℂ)*
      bourgainOscillation (2*Real.pi*((p:ℝ)*q/r))).re = _
    rw [hfac]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he]
  have hh := mul_le_mul hamp hphase (by norm_num : (0:ℝ) ≤ 1/2)
    (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg ha hb) hc))
  calc
    _ = (coreCutoffFloor^3/(primeGaussianHyperbolicConductor m:ℝ))*(1/2) := by ring
    _ ≤ _ := hh

private theorem eventually_core_physical_entry_lower :
    ∀ᶠ m : ℕ in atTop, ∀ r p q : ℕ, (r,p,q) ∈ primeGaussianHyperbolicCore m →
      coreCutoffFloor^3/(4*(primeGaussianHyperbolicConductor m:ℝ)) ≤
        (primeGaussianCubicCoefficient (primeGaussianHyperbolicConductor m) p q r *
          primeGaussianCubicKernel (primeGaussianHyperbolicConductor m) p q r).re := by
  obtain ⟨C,hC,he⟩ := exists_primeGaussianCubic_entry_error
  filter_upwards [tendsto_primeGaussianHyperbolicConductor.eventually_ge_atTop (4*C/coreCutoffFloor^3),
    tendsto_primeGaussianHyperbolicConductor.eventually_gt_atTop 1] with m hm hN
  intro r p q ht
  have hN0 : (0:ℝ) < primeGaussianHyperbolicConductor m := by linarith
  have hg := coreFamily_geometry ht
  have herr := he _ hN p (corePrimeBand_full (coreConductor_pos m) hg.2.1)
    q (corePrimeBand_full (coreConductor_pos m) hg.2.2.1)
    r (corePrimeBand_full (coreConductor_pos m) hg.1)
  have hres := (Complex.abs_re_le_norm _).trans herr
  rw [abs_le] at hres
  have hl := core_main_entry_lower ht
  have hsmall : C/(primeGaussianHyperbolicConductor m:ℝ)^2 ≤ coreCutoffFloor^3/(4*(primeGaussianHyperbolicConductor m:ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm' := (div_le_iff₀ (pow_pos coreCutoffFloor_pos 3)).mp hm
    nlinarith only [mul_le_mul_of_nonneg_right hm' hN0.le]
  simp only [Complex.sub_re] at hres
  have heq : coreCutoffFloor^3/(2*(primeGaussianHyperbolicConductor m:ℝ)) =
      2*(coreCutoffFloor^3/(4*(primeGaussianHyperbolicConductor m:ℝ))) := by ring
  linarith [hres.1]

/-- A noncontracting subfamily of the literal full Gaussian prime cubic has positive
ORIGINAL physical contribution at the contraction scale. Both complete kernel errors
are included. This theorem makes no assertion about the complementary signed sum. -/
theorem exists_primeGaussianHyperbolicCore_physical_mass :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c*(primeGaussianHyperbolicConductor m:ℝ)/(Real.log (primeGaussianHyperbolicConductor m))^2 ≤
        (∑ t ∈ primeGaussianHyperbolicCore m, primeGaussianCubicCoefficient (primeGaussianHyperbolicConductor m) t.2.1 t.2.2 t.1 *
          primeGaussianCubicKernel (primeGaussianHyperbolicConductor m) t.2.1 t.2.2 t.1).re := by
  obtain ⟨c,hc,hcard⟩ := exists_primeGaussianHyperbolicCore_card
  have hv := coreCutoffFloor_pos
  refine ⟨c*coreCutoffFloor^3/4,by positivity,?_⟩
  filter_upwards [hcard,eventually_core_physical_entry_lower,
    tendsto_primeGaussianHyperbolicConductor.eventually_gt_atTop 1] with m hm he hN
  have hN0 : (0:ℝ) < primeGaussianHyperbolicConductor m := by linarith
  have hlog : 0 < Real.log (primeGaussianHyperbolicConductor m:ℝ) := Real.log_pos hN
  calc
    _ = (c*(primeGaussianHyperbolicConductor m:ℝ)^2/(Real.log (primeGaussianHyperbolicConductor m))^2)*
        (coreCutoffFloor^3/(4*(primeGaussianHyperbolicConductor m:ℝ))) := by field_simp
    _ ≤ ((primeGaussianHyperbolicCore m).card:ℝ)*(coreCutoffFloor^3/(4*(primeGaussianHyperbolicConductor m:ℝ))) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = ∑ _t ∈ primeGaussianHyperbolicCore m, coreCutoffFloor^3/(4*(primeGaussianHyperbolicConductor m:ℝ)) := by simp
    _ ≤ _ := by
      rw [Complex.re_sum]
      exact Finset.sum_le_sum (fun t ht => he t.1 t.2.1 t.2.2 ht)

/-- Every selected triple belongs to the literal full prime band, is noncontracting,
and has a small exact hyperbolic gap phase. The tuple order is `(r,p,q)`. -/
theorem primeGaussianHyperbolicCore_mem {m r p q : ℕ}
    (ht : (r,p,q) ∈ primeGaussianHyperbolicCore m) :
    r ∈ primeProfileBand (primeGaussianHyperbolicConductor m:ℝ) ∧
    p ∈ primeProfileBand (primeGaussianHyperbolicConductor m:ℝ) ∧
    q ∈ primeProfileBand (primeGaussianHyperbolicConductor m:ℝ) ∧ p ≠ r ∧ q ≠ r ∧
    |(p:ℝ)-r| * |(q:ℝ)-r| ≤ (primeGaussianHyperbolicConductor m:ℝ)/10000000 := by
  have hg := coreFamily_geometry ht
  exact ⟨corePrimeBand_full (coreConductor_pos m) hg.1,
    corePrimeBand_full (coreConductor_pos m) hg.2.1,
    corePrimeBand_full (coreConductor_pos m) hg.2.2.1,
    hg.2.2.2.1,hg.2.2.2.2.1,by simpa only [coreBase, Nat.cast_ofNat] using hg.2.2.2.2.2⟩

/-- Mesoscopic prime-gap width inside the explicit hyperbolic conductors. -/
def primeGaussianNearWidth (m : ℕ) : ℕ := coreBase^m

theorem primeGaussianNearWidth_pos (m : ℕ) : 0 < primeGaussianNearWidth m :=
  pow_pos coreBase_pos m

theorem primeGaussianNearWidth_pow_four (m : ℕ) :
    primeGaussianNearWidth m ^ 4 = primeGaussianHyperbolicConductor m := by
  dsimp [primeGaussianNearWidth, primeGaussianHyperbolicConductor]
  rw [← pow_mul, Nat.mul_comm m 4]

theorem tendsto_primeGaussianNearWidth :
    Tendsto (fun m : ℕ => (primeGaussianNearWidth m:ℝ)) atTop atTop := by
  simpa only [primeGaussianNearWidth, Nat.cast_pow] using
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num [coreBase] : (1:ℝ) < coreBase)

private theorem nearWidth_le_conductor (m : ℕ) :
    primeGaussianNearWidth m ≤ primeGaussianHyperbolicConductor m := by
  exact Nat.pow_le_pow_right coreBase_pos (by omega)

private theorem nearWidth_near_prime_count {m r : ℕ} (hm : 2 ≤ m)
    (hr : r ∈ corePrimeBand (primeGaussianHyperbolicConductor m)) :
    (((corePrimeBand (primeGaussianHyperbolicConductor m)).filter
      (fun q : ℕ => (coreBase:ℝ)*|(q:ℝ)-r| ≤ primeGaussianNearWidth m)).card:ℝ) ≤
      (primeGaussianNearWidth m:ℝ)/(2048*Real.log (primeGaussianHyperbolicConductor m)) := by
  let N := primeGaussianHyperbolicConductor m
  let h := primeGaussianNearWidth m
  let D : ℝ := (h:ℝ)/(coreBase:ℝ)
  have hN0 : (0:ℝ) < N := by exact_mod_cast coreConductor_pos m
  have hh0 : (0:ℝ) < h := by exact_mod_cast primeGaussianNearWidth_pos m
  have hD0 : 0 < D := div_pos hh0 coreBase_real_pos
  have hhN : (h:ℝ) ≤ N := by exact_mod_cast nearWidth_le_conductor m
  have hDle : D ≤ (N:ℝ)/2 := by
    dsimp [D]
    have hK : (2:ℝ) ≤ coreBase := by norm_num [coreBase]
    exact (div_le_div_of_nonneg_right hhN coreBase_real_pos.le).trans
      (div_le_div_of_nonneg_left hN0.le (by norm_num) hK)
  have hNr : (N:ℝ) ≤ r := by exact_mod_cast (corePrimeBand_frame (coreConductor_pos m) hr).1
  have ha : 0 < (r:ℝ)-D := by linarith
  have hDpow : D = (coreBase:ℝ)^(m-1) := by
    dsimp [D,h,primeGaussianNearWidth]
    rw [Nat.cast_pow, show m = (m-1)+1 by omega, pow_succ]
    exact mul_div_cancel_right₀ _ coreBase_real_pos.ne'
  have hX1 : (1:ℝ) ≤ D := by
    rw [hDpow]
    exact one_le_pow₀ (by norm_num [coreBase])
  have hH : 1 < 2*D := by linarith
  have hklog : 0 < Real.log (coreBase:ℝ) := Real.log_pos (by norm_num [coreBase])
  have hlogN : 0 < Real.log (N:ℝ) := by
    dsimp [N]
    rw [core_log_conductor]
    have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hlogH : Real.log (N:ℝ)/8 ≤ Real.log (2*D) := by
    have hxlog := Real.log_le_log hD0 (show D ≤ 2*D by linarith)
    rw [hDpow, Real.log_pow, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hxlog
    rw [← hDpow] at hxlog
    dsimp [N]
    rw [core_log_conductor]
    have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  let A := (corePrimeBand N).filter (fun q : ℕ => (coreBase:ℝ)*|(q:ℝ)-r| ≤ h)
  have hsub : A ⊆ (Finset.Icc ⌈(r:ℝ)-D⌉₊ ⌊((r:ℝ)-D)+2*D⌋₊).filter Nat.Prime := by
    intro q hq
    obtain ⟨hqS,hqgap⟩ := Finset.mem_filter.mp hq
    have hqp := (corePrimeBand_mem (coreConductor_pos m) hqS).1
    have hgap : |(q:ℝ)-r| ≤ D := (le_div_iff₀ coreBase_real_pos).mpr (by simpa [mul_comm] using hqgap)
    obtain ⟨hlo,hhi⟩ := abs_le.mp hgap
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.ceil_le.mpr (by linarith),Nat.le_floor (by linarith)⟩,hqp⟩
  have hc : (A.card:ℝ) ≤ (BrunTitchmarsh.primesBetween ((r:ℝ)-D) (((r:ℝ)-D)+2*D):ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbt := bagPacket_primesBetween_le_div_log ha hH
  change (A.card:ℝ) ≤ _
  calc
    _ ≤ 292*(2*D)/Real.log (2*D) := hc.trans hbt
    _ ≤ 292*(2*D)/(Real.log (N:ℝ)/8) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlogH
    _ = (4672/(coreBase:ℝ))*((h:ℝ)/Real.log (N:ℝ)) := by dsimp [D]; ring
    _ ≤ (1/2048)*((h:ℝ)/Real.log (N:ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num [coreBase]) (by positivity)
    _ = _ := by ring

/-- Actual central prime pairs with a mesoscopic nonzero gap; tuple order `(r,p)`. -/
def primeGaussianNearPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  (corePrimeBand (primeGaussianHyperbolicConductor m)).biUnion (fun r =>
    (coreFar (corePrimeBand (primeGaussianHyperbolicConductor m))
      (primeGaussianHyperbolicConductor m) (primeGaussianNearWidth m) coreBase r).image
        (fun p => (r,p)))

private theorem card_nearPairs (m : ℕ) :
    (primeGaussianNearPairs m).card =
      ∑ r ∈ corePrimeBand (primeGaussianHyperbolicConductor m),
        (coreFar (corePrimeBand (primeGaussianHyperbolicConductor m))
          (primeGaussianHyperbolicConductor m) (primeGaussianNearWidth m) coreBase r).card := by
  unfold primeGaussianNearPairs
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro r _
    exact Finset.card_image_of_injective _ (fun _ _ hh => (Prod.mk.inj hh).2)
  · intro r _ s _ hrs
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hz
    obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hz'
    exact hrs (congrArg Prod.fst (hp.trans hq.symm))

/-- Global prime mass supplies many nonzero close pairs, with no prime-pair asymptotic. -/
theorem exists_primeGaussianNearPairs_mass :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      c*(primeGaussianHyperbolicConductor m:ℝ)*primeGaussianNearWidth m /
        (Real.log (primeGaussianHyperbolicConductor m))^2 ≤ (primeGaussianNearPairs m).card := by
  obtain ⟨R,hR,hM⟩ := exists_corePrimeBand_mass
  refine ⟨1/262144,by norm_num,?_⟩
  filter_upwards [tendsto_primeGaussianHyperbolicConductor.eventually_ge_atTop R,
    eventually_ge_atTop (2:ℕ)] with m hmR hm
  let N := primeGaussianHyperbolicConductor m
  let h := primeGaussianNearWidth m
  let S := corePrimeBand N
  have hN : 1 < (N:ℝ) := by dsimp [N]; linarith
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos hN
  have hh := primeGaussianNearWidth_pos m
  have hhN := nearWidth_le_conductor m
  have hG := coreAnchors_mass hN hh hh hhN hhN
    (fun x hx => corePrimeBand_frame (coreConductor_pos m) hx) (hM _ hmR)
  have hsub : coreAnchors S N h h ⊆ S := fun _ hx => (Finset.mem_filter.mp hx).1
  rw [card_nearPairs, Nat.cast_sum]
  calc
    _ = (N:ℝ)/(128*Real.log N)*((h:ℝ)/(2048*Real.log N)) := by dsimp [N,h]; ring
    _ ≤ ((coreAnchors S N h h).card:ℝ)*((h:ℝ)/(2048*Real.log N)) :=
      mul_le_mul_of_nonneg_right hG (by positivity)
    _ = ∑ _r ∈ coreAnchors S N h h, (h:ℝ)/(2048*Real.log N) := by simp
    _ ≤ ∑ r ∈ coreAnchors S N h h, ((coreFar S N h coreBase r).card:ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact coreFar_mass hN (Finset.mem_filter.mp hr).2.1
        (nearWidth_near_prime_count hm (hsub hr))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)

/-- Every constructed pair consists of central full-band primes with the declared gap. -/
theorem primeGaussianNearPairs_mem {m r p : ℕ} (ht : (r,p) ∈ primeGaussianNearPairs m) :
    r.Prime ∧ p.Prime ∧
    3*(primeGaussianHyperbolicConductor m:ℝ)/2 < r ∧
    (r:ℝ) ≤ 25*(primeGaussianHyperbolicConductor m)/16 ∧
    3*(primeGaussianHyperbolicConductor m:ℝ)/2 < p ∧
    (p:ℝ) ≤ 25*(primeGaussianHyperbolicConductor m)/16 ∧
    (primeGaussianNearWidth m:ℝ)/10000000 < |(p:ℝ)-r| ∧
    |(p:ℝ)-r| ≤ primeGaussianNearWidth m := by
  obtain ⟨s,hs,ht⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp ht
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  obtain ⟨hcell,hgap⟩ := Finset.mem_filter.mp hq
  have hp := (Finset.mem_filter.mp hcell).1
  have hrm := corePrimeBand_mem (coreConductor_pos m) hs
  have hpm := corePrimeBand_mem (coreConductor_pos m) hp
  refine ⟨hrm.1,hpm.1,hrm.2.1,hrm.2.2,hpm.2.1,hpm.2.2,?_,?_⟩
  · apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 10000000)).mpr
    simpa only [coreBase,Nat.cast_ofNat,mul_comm] using hgap
  · exact coreCell_close (primeGaussianNearWidth_pos m)
      (corePrimeBand_frame (coreConductor_pos m) hp).1
      (corePrimeBand_frame (coreConductor_pos m) hs).1 hcell

end RHTower
