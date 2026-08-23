# AIPL^- / ABCM の Coq 形式化
#   make        すべてビルド（WIP は含まない）
#   make check  主定理の Print Assumptions を確認
#   make clean

COQC ?= coqc
COQFLAGS = -R . ""

# ABCM.v は ~/seminar/abcm-soundness/ABCM.v へのシンボリックリンク（単一の原本）
VS = ABCM.vo AIPLSoundness.vo AIPLSoundness2.vo AIPLSoundness2Example.vo \
     AIPLDining.vo ABCMEmbedding.vo

all: $(VS)

ABCM.vo: ABCM.v
	$(COQC) $(COQFLAGS) ABCM.v
AIPLSoundness.vo: AIPLSoundness.v
	$(COQC) $(COQFLAGS) AIPLSoundness.v
AIPLDining.vo: AIPLDining.v AIPLSoundness.vo
	$(COQC) $(COQFLAGS) AIPLDining.v
ABCMEmbedding.vo: ABCMEmbedding.v AIPLSoundness.vo ABCM.vo
	$(COQC) $(COQFLAGS) ABCMEmbedding.v

# ABCMEmbedding_simulation_WIP.v は未完成なので all に含めない

check: all
	@printf 'Require Import AIPLSoundness AIPLSoundness2 AIPLSoundness2Example AIPLDining ABCMEmbedding.\n\
Print Assumptions no_method_not_understood.\n\
Print Assumptions preservation.\n\
Print Assumptions progress.\n\
Print Assumptions type_safety.\n\
Print Assumptions state_type_invariant.\n\
Print Assumptions future_type_invariant.\n\
Print Assumptions AIPLSoundness2.preservation.\n\
Print Assumptions AIPLSoundness2.type_safety.\n\
Print Assumptions AIPLSoundness2.deadlock_free.\n\
Print Assumptions AIPLSoundness2.progress_total.\n\
Print Assumptions AIPLSoundness2.deadlock_free_star.\n\
Print Assumptions AIPLSoundness2.effect_no_increase.\n\
Print Assumptions AIPLSoundness2.effect_soundness.\n\
Print Assumptions AIPLSoundness2.await_charges_callee.\n\
Print Assumptions AIPLSoundness2.send_does_not_charge.\n\
Print Assumptions ex_not_blocked.\n\
Print Assumptions dining_no_deadlock.\n\
Print Assumptions no_dead_state.\n\
Print Assumptions ordering_is_necessary_and_sufficient.\n\
Print Assumptions tr_ht.\n\
Print Assumptions e_bodies_ok.\n\
Print Assumptions tr_step.\n\
Print Assumptions tr_estep.\n\
Print Assumptions abcm_translation_never_stuck.\n' > _chk.v
	@$(COQC) $(COQFLAGS) _chk.v 2>/dev/null | grep -v '^$$'
	@rm -f _chk.v _chk.vo* _chk.glob

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux _chk.v

.PHONY: all check clean
