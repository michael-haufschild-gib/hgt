import GaloisForLFunctions.HTGeometry.FixedSourceFormationCapital

/-!
# Sufficient-macro saturation

Section 6 of the formation-resource card `ULF-FRM-2`.

For a finite one-parameter exponential family `(FCAP.26)` with sum statistic `(FCAP.27)`:

* `(FCAP.28)`–`(FCAP.30)`  the fibre weight, the macro law and the common recovery kernel;
* `(FCAP.31)`, `(FCAP.32)`  **Theorem 6.1** items 1–3: the statistic pushes the product packet onto
  the macro law, and the `θ`-independent recovery kernel reconstructs the independent product;
* `(FCAP.33)`, `(FCAP.35a)`  the whole Rényi capital spectrum of the macro pair is exactly `d`
  times the one-packet spectrum, by data processing in *both* directions;
* `(FCAP.35)`  the macro Fisher information is exactly `d` times the one-packet Fisher
  information, proved from explicit product marginals.

Everything is unconditional and finite.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace SufficientMacro

variable {X : Type*} [Fintype X] [DecidableEq X] (b T : X → ℝ)

/-- `(FCAP.26)`  Partition function of a finite one-parameter exponential family. -/
def partition (θ : ℝ) : ℝ := ∑ x, b x * Real.exp (θ * T x)

omit [DecidableEq X] in
theorem partition_pos (hb : ∀ x, 0 < b x) [Nonempty X] (θ : ℝ) : 0 < partition b T θ :=
  Finset.sum_pos (fun x _ => mul_pos (hb x) (Real.exp_pos _)) ⟨Classical.arbitrary X, by simp⟩

/-- `(FCAP.26)`  The exponential-family packet. -/
def packet (θ : ℝ) : X → ℝ := fun x => b x * Real.exp (θ * T x) / partition b T θ

omit [DecidableEq X] in
theorem packet_nonneg (hb : ∀ x, 0 < b x) [Nonempty X] (θ : ℝ) (x : X) : 0 ≤ packet b T θ x :=
  div_nonneg (mul_nonneg (hb x).le (Real.exp_nonneg _)) (partition_pos b T hb θ).le

omit [DecidableEq X] in
theorem packet_sum (hb : ∀ x, 0 < b x) [Nonempty X] (θ : ℝ) : ∑ x, packet b T θ x = 1 := by
  have h : ∑ x, packet b T θ x
      = (∑ x, b x * Real.exp (θ * T x)) / partition b T θ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => rfl
  rw [h, ← partition]
  exact div_self (partition_pos b T hb θ).ne'

/-- `(FCAP.27)`  The sum statistic of depth `d`. -/
def sumStat (d : ℕ) : (Fin d → X) → ℝ := fun x => ∑ j, T (x j)

/-- The finite image of the sum statistic. -/
def statImage (d : ℕ) : Finset ℝ := Finset.univ.image (sumStat T d)

omit [DecidableEq X] in
theorem sumStat_mem (d : ℕ) (x : Fin d → X) : sumStat T d x ∈ statImage T d :=
  Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- The macro alphabet. -/
abbrev MacroAlphabet (d : ℕ) := {t : ℝ // t ∈ statImage T d}

/-- `(FCAP.28)`  The fibre weight. -/
def fibreWeight (d : ℕ) (t : ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin d → X => sumStat T d x = t), ∏ j, b (x j)

omit [DecidableEq X] in
theorem fibreWeight_pos (hb : ∀ x, 0 < b x) (d : ℕ) {t : ℝ} (ht : t ∈ statImage T d) :
    0 < fibreWeight b T d t := by
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp ht
  refine Finset.sum_pos (fun y _ => Finset.prod_pos fun j _ => hb (y j)) ⟨x, ?_⟩
  simp [hx]

/-- `(FCAP.29)`  The macro law. -/
def macroPacket (d : ℕ) (θ : ℝ) : MacroAlphabet T d → ℝ :=
  fun t => fibreWeight b T d t.1 * Real.exp (θ * t.1) / partition b T θ ^ d

/-- `(FCAP.30)`  The common recovery kernel. -/
def recoveryWeight (d : ℕ) (t : ℝ) (x : Fin d → X) : ℝ :=
  if sumStat T d x = t then (∏ j, b (x j)) / fibreWeight b T d t else 0

omit [DecidableEq X] in
theorem tensorPower_packet (hb : ∀ x, 0 < b x) [Nonempty X] (θ : ℝ) (d : ℕ) (x : Fin d → X) :
    tensorPower d (packet b T θ) x
      = (∏ j, b (x j)) * Real.exp (θ * sumStat T d x) / partition b T θ ^ d := by
  have hZ : partition b T θ ≠ 0 := (partition_pos b T hb θ).ne'
  rw [tensorPower]
  have hstep : ∀ j : Fin d, packet b T θ (x j)
      = (b (x j) * Real.exp (θ * T (x j))) / partition b T θ := fun j => rfl
  rw [Finset.prod_congr rfl fun j _ => hstep j, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib,
    ← Real.exp_sum]
  congr 2
  rw [sumStat, Finset.mul_sum]

omit [DecidableEq X] in
/-- **`(FCAP.31)`.**  The sum statistic pushes the product packet onto the macro law. -/
theorem sum_fibre_tensorPower (hb : ∀ x, 0 < b x) [Nonempty X] (θ : ℝ) (d : ℕ)
    (t : MacroAlphabet T d) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin d → X => sumStat T d x = t.1),
        tensorPower d (packet b T θ) x = macroPacket b T d θ t := by
  rw [macroPacket, fibreWeight, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxt : sumStat T d x = t.1 := (Finset.mem_filter.mp hx).2
  rw [tensorPower_packet b T hb θ d x, hxt]

omit [DecidableEq X] in
/-- `(FCAP.30)`  The recovery kernel is a probability kernel. -/
theorem sum_recoveryWeight (hb : ∀ x, 0 < b x) (d : ℕ) (t : MacroAlphabet T d) :
    ∑ x : Fin d → X, recoveryWeight b T d t.1 x = 1 := by
  have hpos := fibreWeight_pos b T hb d t.2
  have hstep : ∀ x : Fin d → X, recoveryWeight b T d t.1 x
      = if sumStat T d x = t.1 then (∏ j, b (x j)) / fibreWeight b T d t.1 else 0 :=
    fun x => rfl
  rw [Finset.sum_congr rfl fun x _ => hstep x, ← Finset.sum_filter, ← Finset.sum_div,
    ← fibreWeight]
  exact div_self hpos.ne'

omit [DecidableEq X] in
/-- **`(FCAP.32)`.**  Common recovery reconstructs the independent product. -/
theorem sum_macro_recovery (hb : ∀ x, 0 < b x) [Nonempty X] (θ : ℝ) (d : ℕ) (x : Fin d → X) :
    ∑ t : MacroAlphabet T d, recoveryWeight b T d t.1 x * macroPacket b T d θ t
      = tensorPower d (packet b T θ) x := by
  classical
  have hZ : (0:ℝ) < partition b T θ := partition_pos b T hb θ
  set t₀ : MacroAlphabet T d := ⟨sumStat T d x, sumStat_mem T d x⟩ with ht₀
  rw [Finset.sum_eq_single t₀ ?_ ?_]
  · have hrec : recoveryWeight b T d t₀.1 x
        = (∏ j, b (x j)) / fibreWeight b T d (sumStat T d x) := by
      show (if sumStat T d x = t₀.1 then (∏ j, b (x j)) / fibreWeight b T d t₀.1 else 0) = _
      rw [if_pos rfl]
    have hpos := fibreWeight_pos b T hb d (sumStat_mem T d x)
    rw [hrec, macroPacket, tensorPower_packet b T hb θ d x]
    show (∏ j, b (x j)) / fibreWeight b T d (sumStat T d x)
        * (fibreWeight b T d (sumStat T d x) * Real.exp (θ * sumStat T d x)
          / partition b T θ ^ d) = _
    field_simp
  · intro t _ hne
    have hzero : recoveryWeight b T d t.1 x = 0 := by
      show (if sumStat T d x = t.1 then (∏ j, b (x j)) / fibreWeight b T d t.1 else 0) = 0
      rw [if_neg (fun h => hne (Subtype.ext h.symm))]
    rw [hzero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ t₀) h

/-- The deterministic sufficient statistic, as a Markov kernel. -/
def statKernel (d : ℕ) : FiniteMarkovKernel (Fin d → X) (MacroAlphabet T d) where
  weight t x := if t.1 = sumStat T d x then 1 else 0
  nonneg t x := by split <;> norm_num
  column_sum x := by
    classical
    rw [Finset.sum_eq_single (⟨sumStat T d x, sumStat_mem T d x⟩ : MacroAlphabet T d)]
    · simp
    · intro t _ hne
      exact if_neg (fun h => hne (Subtype.ext h))
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The common recovery kernel `(FCAP.30)`. -/
def recoveryKernel (hb : ∀ x, 0 < b x) (d : ℕ) :
    FiniteMarkovKernel (MacroAlphabet T d) (Fin d → X) where
  weight x t := recoveryWeight b T d t.1 x
  nonneg x t := by
    show (0:ℝ) ≤ if sumStat T d x = t.1 then (∏ j, b (x j)) / fibreWeight b T d t.1 else 0
    split
    · exact div_nonneg (Finset.prod_nonneg fun j _ => (hb (x j)).le)
        (fibreWeight_pos b T hb d t.2).le
    · exact le_rfl
  column_sum t := sum_recoveryWeight b T hb d t

omit [DecidableEq X] in
theorem statKernel_applyReal (hb : ∀ x, 0 < b x) [Nonempty X] (θ : ℝ) (d : ℕ) :
    (statKernel T d).toFinitePositiveKernel.applyReal (tensorPower d (packet b T θ))
      = macroPacket b T d θ := by
  classical
  funext t
  rw [FinitePositiveKernel.applyReal, ← sum_fibre_tensorPower b T hb θ d t, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  show (if t.1 = sumStat T d x then (1:ℝ) else 0) * tensorPower d (packet b T θ) x
    = if sumStat T d x = t.1 then tensorPower d (packet b T θ) x else 0
  by_cases h : sumStat T d x = t.1
  · rw [if_pos h.symm, if_pos h, one_mul]
  · rw [if_neg (fun h' => h h'.symm), if_neg h, zero_mul]

omit [DecidableEq X] in
theorem recoveryKernel_applyReal (hb : ∀ x, 0 < b x) [Nonempty X] (θ : ℝ) (d : ℕ) :
    (recoveryKernel b T hb d).toFinitePositiveKernel.applyReal (macroPacket b T d θ)
      = tensorPower d (packet b T θ) := by
  funext x
  rw [FinitePositiveKernel.applyReal]
  exact sum_macro_recovery b T hb θ d x

omit [DecidableEq X] in
theorem macroPacket_nonneg (hb : ∀ x, 0 < b x) [Nonempty X] (d : ℕ) (θ : ℝ)
    (t : MacroAlphabet T d) : 0 ≤ macroPacket b T d θ t := by
  rw [← statKernel_applyReal b T hb θ d]
  exact FinitePositiveKernel.applyReal_nonneg _
    (tensorPower_nonneg d (packet_nonneg b T hb θ)) t

theorem macroPacket_sum (hb : ∀ x, 0 < b x) [Nonempty X] (d : ℕ) (θ : ℝ) :
    ∑ t, macroPacket b T d θ t = 1 := by
  rw [← statKernel_applyReal b T hb θ d, FiniteMarkovKernel.sum_applyReal,
    sum_tensorPower, packet_sum b T hb θ, one_pow]

/-- **Theorem 6.1, `(FCAP.33)`, `(FCAP.35a)`.**  The sufficient macropacket attains the whole
Rényi capital bound exactly. -/
theorem renyiOverlap_macroPacket {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (hb : ∀ x, 0 < b x)
    [Nonempty X] (d : ℕ) (θ φ : ℝ) :
    renyiOverlap α (macroPacket b T d θ) (macroPacket b T d φ)
      = renyiOverlap α (packet b T θ) (packet b T φ) ^ d := by
  have hp : ∀ ψ : ℝ, ∀ x, 0 ≤ packet b T ψ x := fun ψ => packet_nonneg b T hb ψ
  have htp : ∀ ψ : ℝ, ∀ x, 0 ≤ tensorPower d (packet b T ψ) x :=
    fun ψ => tensorPower_nonneg d (hp ψ)
  have hmp : ∀ ψ : ℝ, ∀ t, 0 ≤ macroPacket b T d ψ t := fun ψ => macroPacket_nonneg b T hb d ψ
  have h1' := renyiOverlap_markovDataProcessing h0 h1 (statKernel T d) (htp θ) (htp φ)
  rw [statKernel_applyReal b T hb θ d, statKernel_applyReal b T hb φ d] at h1'
  have h2' := renyiOverlap_markovDataProcessing h0 h1 (recoveryKernel b T hb d) (hmp θ) (hmp φ)
  rw [recoveryKernel_applyReal b T hb θ d, recoveryKernel_applyReal b T hb φ d] at h2'
  have heq : renyiOverlap α (tensorPower d (packet b T θ)) (tensorPower d (packet b T φ))
      = renyiOverlap α (macroPacket b T d θ) (macroPacket b T d φ) := le_antisymm h1' h2'
  rw [← heq]
  exact renyiOverlap_tensorPower _ d (hp θ) (hp φ)

/-- **`(FCAP.33)`.**  The Hellinger form. -/
theorem finitePacketAffinity_macroPacket (hb : ∀ x, 0 < b x) [Nonempty X] (d : ℕ) (θ φ : ℝ) :
    finitePacketAffinity (macroPacket b T d θ) (macroPacket b T d φ)
      = finitePacketAffinity (packet b T θ) (packet b T φ) ^ d :=
  renyiOverlap_macroPacket b T (by norm_num) (by norm_num) hb d θ φ

/-! ## Product marginals -/

omit [DecidableEq X] in
theorem sum_tensorPower_mul_single (p : X → ℝ) (d : ℕ) (j₀ : Fin d) (F : X → ℝ)
    (hp1 : ∑ y, p y = 1) :
    ∑ x : Fin d → X, tensorPower d p x * F (x j₀) = ∑ y, p y * F y := by
  classical
  set h : Fin d → X → ℝ := fun i y => if i = j₀ then p y * F y else p y with hh
  have hterm : ∀ x : Fin d → X, tensorPower d p x * F (x j₀) = ∏ i, h i (x i) := by
    intro x
    rw [tensorPower, ← Finset.mul_prod_erase Finset.univ (fun i => p (x i)) (Finset.mem_univ j₀),
      ← Finset.mul_prod_erase Finset.univ (fun i => h i (x i)) (Finset.mem_univ j₀)]
    have he : ∀ i ∈ Finset.univ.erase j₀, h i (x i) = p (x i) := fun i hi => by
      rw [hh]; exact if_neg (Finset.ne_of_mem_erase hi)
    have hj : h j₀ (x j₀) = p (x j₀) * F (x j₀) := by rw [hh]; exact if_pos rfl
    rw [Finset.prod_congr rfl he, hj]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  have hprod := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset X)) h
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod, ← Finset.mul_prod_erase Finset.univ (fun i => ∑ y, h i y) (Finset.mem_univ j₀)]
  have hone : ∀ i ∈ Finset.univ.erase j₀, (∑ y, h i y) = 1 := by
    intro i hi
    have hpi : ∀ y, h i y = p y := fun y => by rw [hh]; exact if_neg (Finset.ne_of_mem_erase hi)
    rw [Finset.sum_congr rfl fun y _ => hpi y]
    exact hp1
  have hj : (∑ y, h j₀ y) = ∑ y, p y * F y :=
    Finset.sum_congr rfl fun y _ => by rw [hh]; exact if_pos rfl
  rw [Finset.prod_congr rfl hone, Finset.prod_const_one, mul_one, hj]

omit [DecidableEq X] in
theorem sum_tensorPower_mul_pair (p : X → ℝ) (d : ℕ) {j k : Fin d} (hjk : j ≠ k)
    (F G : X → ℝ) (hp1 : ∑ y, p y = 1) :
    ∑ x : Fin d → X, tensorPower d p x * (F (x j) * G (x k))
      = (∑ y, p y * F y) * (∑ y, p y * G y) := by
  classical
  set h : Fin d → X → ℝ :=
    fun i y => if i = j then p y * F y else if i = k then p y * G y else p y with hh
  have hterm : ∀ x : Fin d → X,
      tensorPower d p x * (F (x j) * G (x k)) = ∏ i, h i (x i) := by
    intro x
    have hsplit : ∀ (g : Fin d → ℝ), ∏ i, g i
        = g j * (g k * ∏ i ∈ (Finset.univ.erase j).erase k, g i) := by
      intro g
      rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ j)]
      congr 1
      exact (Finset.mul_prod_erase _ g (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)).symm
    rw [tensorPower, hsplit (fun i => p (x i)), hsplit (fun i => h i (x i))]
    have he : ∀ i ∈ (Finset.univ.erase j).erase k, h i (x i) = p (x i) := by
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      rw [hh]
      simp only []
      rw [if_neg hij, if_neg hik]
    have hjv : h j (x j) = p (x j) * F (x j) := by rw [hh]; exact if_pos rfl
    have hkv : h k (x k) = p (x k) * G (x k) := by
      rw [hh]
      simp only []
      rw [if_neg (Ne.symm hjk)]
      simp
    rw [Finset.prod_congr rfl he, hjv, hkv]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  have hprod := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset X)) h
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  have hsplit : ∀ (g : Fin d → ℝ), ∏ i, g i
      = g j * (g k * ∏ i ∈ (Finset.univ.erase j).erase k, g i) := by
    intro g
    rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ j)]
    congr 1
    exact (Finset.mul_prod_erase _ g (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)).symm
  rw [hsplit (fun i => ∑ y, h i y)]
  have hone : ∀ i ∈ (Finset.univ.erase j).erase k, (∑ y, h i y) = 1 := by
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hpi : ∀ y, h i y = p y := fun y => by
      rw [hh]; simp only []; rw [if_neg hij, if_neg hik]
    rw [Finset.sum_congr rfl fun y _ => hpi y]
    exact hp1
  have hjv : (∑ y, h j y) = ∑ y, p y * F y :=
    Finset.sum_congr rfl fun y _ => by rw [hh]; exact if_pos rfl
  have hkv : (∑ y, h k y) = ∑ y, p y * G y :=
    Finset.sum_congr rfl fun y _ => by
      rw [hh]; simp only []; rw [if_neg (Ne.symm hjk)]; simp
  rw [Finset.prod_congr rfl hone, Finset.prod_const_one, mul_one, hjv, hkv]

/-! ## Fisher information -/

/-- `(FCAP.35)`  Fisher information of a finite packet against an observable. -/
def fisherInfo {Y : Type*} [Fintype Y] (q : Y → ℝ) (f : Y → ℝ) : ℝ :=
  ∑ y, q y * (f y - ∑ z, q z * f z) ^ 2

omit [DecidableEq X] in
theorem sum_macroPacket_mul (hb : ∀ x, 0 < b x) [Nonempty X] (d : ℕ) (θ : ℝ) (g : ℝ → ℝ) :
    ∑ t : MacroAlphabet T d, macroPacket b T d θ t * g t.1
      = ∑ x : Fin d → X, tensorPower d (packet b T θ) x * g (sumStat T d x) := by
  classical
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Fin d → X)),
      (⟨sumStat T d x, sumStat_mem T d x⟩ : MacroAlphabet T d)
        ∈ (Finset.univ : Finset (MacroAlphabet T d)) := fun x _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun x => tensorPower d (packet b T θ) x * g (sumStat T d x))]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hfilter : (Finset.univ.filter
      fun x : Fin d → X => (⟨sumStat T d x, sumStat_mem T d x⟩ : MacroAlphabet T d) = t)
      = Finset.univ.filter (fun x : Fin d → X => sumStat T d x = t.1) := by
    refine Finset.filter_congr fun x _ => ?_
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  rw [hfilter]
  have hinner : ∀ x ∈ Finset.univ.filter (fun x : Fin d → X => sumStat T d x = t.1),
      tensorPower d (packet b T θ) x * g (sumStat T d x)
        = tensorPower d (packet b T θ) x * g t.1 := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, sum_fibre_tensorPower b T hb θ d t]

omit [DecidableEq X] in
/-- **`(FCAP.35)`.**  The macro Fisher information is `d` times the one-packet Fisher
information. -/
theorem fisherInfo_macroPacket (hb : ∀ x, 0 < b x) [Nonempty X] (d : ℕ) (θ : ℝ) :
    fisherInfo (macroPacket b T d θ) (fun t => t.1) = d * fisherInfo (packet b T θ) T := by
  classical
  set p := packet b T θ with hp
  set μ := ∑ y, p y * T y with hμ
  have hp1 : ∑ y, p y = 1 := packet_sum b T hb θ
  have hcentre : ∑ y, p y * (T y - μ) = 0 := by
    have : ∑ y, p y * (T y - μ) = (∑ y, p y * T y) - μ * ∑ y, p y := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [this, hp1, ← hμ]
    ring
  have hmean : ∑ t : MacroAlphabet T d, macroPacket b T d θ t * t.1 = d * μ := by
    rw [sum_macroPacket_mul b T hb d θ (fun t => t)]
    have hexp : ∀ x : Fin d → X, tensorPower d p x * sumStat T d x
        = ∑ j, tensorPower d p x * T (x j) := by
      intro x
      rw [sumStat, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x _ => hexp x, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j _ => sum_tensorPower_mul_single p d j T hp1]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hμ]
  rw [fisherInfo, Finset.sum_congr rfl fun t _ => (by rw [hmean] :
    macroPacket b T d θ t * (t.1 - ∑ z, macroPacket b T d θ z * z.1) ^ 2
      = macroPacket b T d θ t * (t.1 - (d : ℝ) * μ) ^ 2)]
  rw [sum_macroPacket_mul b T hb d θ (fun t => (t - (d : ℝ) * μ) ^ 2)]
  have hexpand : ∀ x : Fin d → X,
      tensorPower d p x * (sumStat T d x - (d : ℝ) * μ) ^ 2
        = ∑ j, ∑ k, tensorPower d p x * ((T (x j) - μ) * (T (x k) - μ)) := by
    intro x
    have hs : sumStat T d x - (d : ℝ) * μ = ∑ j, (T (x j) - μ) := by
      rw [sumStat, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hs, sq, Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => hexpand x]
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin d, (∑ x : Fin d → X, ∑ k,
      tensorPower d p x * ((T (x j) - μ) * (T (x k) - μ)))
        = fisherInfo p T := by
    intro j
    rw [Finset.sum_comm]
    have hterm : ∀ k : Fin d, ∑ x : Fin d → X,
        tensorPower d p x * ((T (x j) - μ) * (T (x k) - μ))
          = if k = j then fisherInfo p T else 0 := by
      intro k
      by_cases hk : k = j
      · subst hk
        rw [if_pos rfl]
        have := sum_tensorPower_mul_single p d k (fun y => (T y - μ) * (T y - μ)) hp1
        rw [this, fisherInfo, ← hμ]
        exact Finset.sum_congr rfl fun y _ => by rw [sq]
      · rw [if_neg hk]
        have := sum_tensorPower_mul_pair p d (Ne.symm hk) (fun y => T y - μ)
          (fun y => T y - μ) hp1
        rw [this, hcentre, mul_zero]
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    simp
  rw [Finset.sum_congr rfl fun j _ => hinner j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-! ## §7  Functional-equation equivariance -/

section Reflection

variable {X : Type*} [Fintype X] [DecidableEq X] {b T : X → ℝ}
  (R : Equiv.Perm X) (hR : ∀ x, R (R x) = x) (hb : ∀ x, b (R x) = b x) (hT : ∀ x, T (R x) = -T x)

include hb hT in
omit [DecidableEq X] in
/-- `(FCAP.37)`  The partition function is reflection symmetric. -/
theorem partition_reflect (θ : ℝ) : partition b T (-θ) = partition b T θ := by
  rw [partition, partition, ← Equiv.sum_comp R (fun x => b x * Real.exp (θ * T x))]
  exact Finset.sum_congr rfl fun x _ => by rw [hb x, hT x]; ring_nf

include hb hT in
omit [DecidableEq X] in
/-- `(FCAP.37)`  Reflection reverses the canonical parameter. -/
theorem packet_reflect (θ : ℝ) (x : X) : packet b T (-θ) x = packet b T θ (R x) := by
  rw [packet, packet, partition_reflect R hb hT θ, hb x, hT x]
  ring_nf

include hT in
omit [Fintype X] [DecidableEq X] in
theorem sumStat_reflect (d : ℕ) (x : Fin d → X) :
    sumStat T d (fun j => R (x j)) = -sumStat T d x := by
  rw [sumStat, sumStat, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hT (x j)

include hT in
omit [DecidableEq X] in
theorem statImage_neg_mem {d : ℕ} {t : ℝ} (ht : t ∈ statImage T d) : -t ∈ statImage T d := by
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp ht
  refine Finset.mem_image.mpr ⟨fun j => R (x j), Finset.mem_univ _, ?_⟩
  rw [sumStat_reflect R hT d x, hx]

include hR hb hT in
omit [DecidableEq X] in
/-- `(FCAP.38)`  The fibre weight is reflection symmetric. -/
theorem fibreWeight_reflect (d : ℕ) (t : ℝ) :
    fibreWeight b T d (-t) = fibreWeight b T d t := by
  classical
  rw [fibreWeight, fibreWeight]
  refine Finset.sum_nbij' (fun x => fun j => R (x j)) (fun y => fun j => R (y j)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [sumStat_reflect R hT d x, hx.2]
    ring
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [sumStat_reflect R hT d y, hy.2]
  · intro x _
    funext j
    exact hR (x j)
  · intro y _
    funext j
    exact hR (y j)
  · intro x _
    exact Finset.prod_congr rfl fun j _ => (hb (x j)).symm

include hR hb hT in
omit [DecidableEq X] in
/-- `(FCAP.37)`  The macro law reverses the canonical parameter. -/
theorem macroPacket_reflect (d : ℕ) (θ : ℝ) (t : MacroAlphabet T d) :
    macroPacket b T d (-θ) t
      = macroPacket b T d θ ⟨-t.1, statImage_neg_mem R hT t.2⟩ := by
  rw [macroPacket, macroPacket, partition_reflect R hb hT θ]
  show fibreWeight b T d t.1 * Real.exp (-θ * t.1) / partition b T θ ^ d
    = fibreWeight b T d (-t.1) * Real.exp (θ * -t.1) / partition b T θ ^ d
  rw [fibreWeight_reflect R hR hb hT d t.1]
  ring_nf

include hR hb hT in
omit [DecidableEq X] in
/-- `(FCAP.38)`  The recovery kernel is reflection equivariant. -/
theorem recoveryWeight_reflect (d : ℕ) (t : ℝ) (x : Fin d → X) :
    recoveryWeight b T d (-t) (fun j => R (x j)) = recoveryWeight b T d t x := by
  show (if sumStat T d (fun j => R (x j)) = -t then
      (∏ j, b (R (x j))) / fibreWeight b T d (-t) else 0)
    = if sumStat T d x = t then (∏ j, b (x j)) / fibreWeight b T d t else 0
  rw [sumStat_reflect R hT d x, fibreWeight_reflect R hR hb hT d t,
    Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) => hb (x j)]
  by_cases h : sumStat T d x = t
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hc => h (neg_injective hc))]

end Reflection

end SufficientMacro

end

end GaloisForLFunctions.HTGeometry
