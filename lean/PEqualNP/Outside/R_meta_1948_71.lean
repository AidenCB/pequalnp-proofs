import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1948_71
    (hsound : ∀ (n k : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S : Finset (Fin n)),
      PEqualNP.ReadK.readsAtMost C n (PEqualNP.ReadK.setList S) k = true →
      PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.ReadK.setInput S) = true)
    (hfind : ∃ (q N : ℕ) (L : Fin N → Finset (Fin N))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q ∧ N = q ^ 2 + q + 1 ∧ (∀ l, (L l).card = q + 1) ∧
      (∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ L l ∧ p' ∈ L l) ∧
      PEqualNP.TopForm.IsAO2 (N + N) C ∧ 100 * C.size < N * q ∧
      (∀ p l : Fin N, p ∈ L l →
        PEqualNP.ReadK.readsAtMost C (N + N)
          (PEqualNP.ReadK.setList {Fin.castAdd N p, Fin.natAdd N l}) 2 = true) ∧
      (∀ P : Finset (Fin N),
        (∀ p : Fin N, p ∉ P → ∃ l : Fin N, p ∈ L l ∧ Disjoint P (L l)) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C
        (Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (Disjoint P (L l)))) = false)) :
    ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) := by
  classical
  intro bound
  obtain ⟨q, N, L, C, hq, hN, hcard, huniq, hAO, hcost, hpair, havoid⟩ := hfind
  have mono : Monotone (PEqualNP.MetaComplexity.circuitFun (N + N) C) := by
    let dom (a b : List Bool) := ∀ i, a.getD i false = true → b.getD i false = true
    let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have gateMono (op : PEqualNP.CircuitLowerBounds.GateOp) (hop : op = .and ∨ op = .or)
        (inputs : List ℕ) (a b : List Bool) (hab : dom a b) :
        op.eval (inputs.map fun i => a.getD i false) = true →
        op.eval (inputs.map fun i => b.getD i false) = true := by
      rcases hop with rfl | rfl
      · change (inputs.map (fun i => a.getD i false)).all id = true →
            (inputs.map (fun i => b.getD i false)).all id = true
        simp only [List.all_eq_true, List.mem_map, id]
        intro h v hv
        obtain ⟨i, hi, rfl⟩ := hv
        exact hab i (h _ ⟨i, hi, rfl⟩)
      · change (inputs.map (fun i => a.getD i false)).any id = true →
            (inputs.map (fun i => b.getD i false)).any id = true
        simp only [List.any_eq_true, List.mem_map, id]
        rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
        exact ⟨_, ⟨i, hi, rfl⟩, hab i hv⟩
    have foldMono (gs : List PEqualNP.CircuitLowerBounds.Gate)
        (allowed : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
        ∀ a b : List Bool, a.length = b.length → dom a b → dom (gs.foldl step a) (gs.foldl step b) := by
      induction gs with
      | nil => intro a b _ hab; exact hab
      | cons g gs ih =>
        intro a b len hab
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (fun g' hg' => allowed g' (List.mem_cons_of_mem _ hg'))
        · simp [step, len]
        · intro i hi
          unfold step at hi ⊢
          by_cases left : i < a.length
          · rw [List.getD_append _ _ _ _ left] at hi
            rw [List.getD_append _ _ _ _ (by omega)]
            exact hab i hi
          · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
            rw [List.getD_append_right _ _ _ _ (by omega), ← len]
            cases offset : i - a.length with
            | zero =>
              rw [offset] at hi
              exact gateMono g.op (allowed g List.mem_cons_self) g.inputs a b hab hi
            | succ k =>
              rw [offset] at hi
              simp at hi
    intro x y hxy
    apply Bool.le_iff_imp.mpr
    refine foldMono C.gates hAO.1 (List.ofFn x) (List.ofFn y) (by simp) ?_ C.output
    intro i hi
    by_cases hin : i < N + N
    · rw [List.getD_eq_getElem _ _ (by simpa using hin)] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hin)]
      simp only [List.getElem_ofFn] at hi ⊢
      exact Bool.le_iff_imp.mp (hxy _) hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hin)] at hi
      contradiction
  have correct (z : Fin (N + N) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, p ∈ L l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true) := by
    by_cases good : ∃ p l : Fin N, p ∈ L l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true
    · rw [decide_eq_true good]
      obtain ⟨p, l, inc, hp, hl⟩ := good
      let T : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l}
      have acc := hsound _ 2 C T (hpair p l inc)
      have below : PEqualNP.ReadK.setInput T ≤ z := by
        intro i
        by_cases hi : i ∈ T
        · rcases Finset.mem_insert.mp hi with hi | hi
          · subst i
            rw [hp]
            exact Bool.le_true _
          · have eq := Finset.mem_singleton.mp hi
            subst i
            rw [hl]
            exact Bool.le_true _
        · change decide (i ∈ T) ≤ z i
          simp [hi]
      have hz := mono below
      exact Bool.le_iff_imp.mp hz acc
    · rw [decide_eq_false good]
      let P : Finset (Fin N) := Finset.univ.filter fun p =>
        ∀ l : Fin N, z (Fin.natAdd N l) = true → p ∉ L l
      have memP {p : Fin N} : p ∈ P ↔ ∀ l : Fin N, z (Fin.natAdd N l) = true → p ∉ L l := by
        simp [P]
      have disjointLine {l : Fin N} (hl : z (Fin.natAdd N l) = true) : Disjoint P (L l) :=
        Finset.disjoint_left.mpr fun _ hp => (memP.mp hp) l hl
      have closedP (p : Fin N) (hp : p ∉ P) : ∃ l : Fin N, p ∈ L l ∧ Disjoint P (L l) := by
        by_contra miss
        apply hp
        exact memP.mpr fun l hl inc => miss ⟨l, inc, disjointLine hl⟩
      let v : Fin (N + N) → Bool := Fin.addCases (fun p => decide (p ∈ P))
        (fun l => decide (Disjoint P (L l)))
      have below : z ≤ v := by
        intro i
        refine Fin.addCases (fun p => ?_) (fun l => ?_) i
        · cases hp : z (Fin.castAdd N p) with
          | false => simp
          | true =>
            have mem : p ∈ P := memP.mpr fun l hl inc => good ⟨p, l, inc, hp, hl⟩
            simp [v, mem]
        · cases hl : z (Fin.natAdd N l) with
          | false => simp
          | true =>
            simp only [v, Fin.addCases_right, decide_eq_true (disjointLine hl), le_refl]
      have hz := mono below
      have rejected : PEqualNP.MetaComplexity.circuitFun (N + N) C v = false := havoid P closedP
      rw [rejected] at hz
      exact le_antisymm hz (Bool.false_le _)
  have readTwo : PEqualNP.ReadK.IsReadK (N + N) C 2 := by
    intro S hS
    obtain ⟨accept, minimal⟩ := hS
    rw [correct] at accept
    obtain ⟨p, l, inc, hp, hl⟩ := of_decide_eq_true accept
    let T : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l}
    have pairReads : PEqualNP.ReadK.readsAtMost C (N + N) (PEqualNP.ReadK.setList T) 2 = true :=
      hpair p l inc
    have sub : T ⊆ S := Finset.insert_subset (of_decide_eq_true hp)
      (Finset.singleton_subset_iff.mpr (of_decide_eq_true hl))
    by_cases same : T = S
    · rwa [← same]
    · have lt : T ⊂ S := lt_of_le_of_ne sub same
      have off := minimal T (Finset.mem_ssubsets.mpr lt)
      have on := hsound _ 2 C T pairReads
      simp [on] at off
  have cards (l : Fin N) : (Finset.univ.filter (fun p => p ∈ L l)).card = q + 1 := by
    simpa using hcard l
  exact (Nat.not_le_of_lt hcost)
    (bound q N (fun p l => p ∈ L l) C hq hN cards huniq hAO correct readTwo)
