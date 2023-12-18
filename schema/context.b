MACHINE generic
SETS
	tp_RouteSubClass = {T_RSC_P, T_RSC_NP};
	tp_StaffProtectionKindType = {T_Staff, T_PLOD};
	tp_SubRoute = {T_UAA_AB, T_UAC_CB, T_UAC_CA, T_UAC_BC, T_UAD_BD, T_UAD_BC, T_UAC_DA, T_UAF_BA, T_UBB_BA, T_UAB_BA, T_UAD_DB, T_UAD_DA, T_UAB_AB, T_UAD_CB, T_UAC_AC};
	tp_SignalType = {T_ST_BlockMarkerAutomatic, T_ST_Fringe, T_ST_CoActing, T_ST_BlockMarkerControlled, T_ST_Distant, T_ST_Buffer, T_ST_Controlled, T_ST_PresetShunt, T_ST_Preliminary, T_ST_StopBoard, T_ST_Shunt, T_ST_VirtualBidirectional, T_ST_FixedRed, T_ST_FixedDistantBoard, T_ST_Banner_Repeater, T_ST_Automatic, T_ST_LimitOfShunt};
	tp_RouteClass = {T_RC_EA, T_AutomaticMain, T_A, T_B, T_C, T_M, T_P, T_S, T_U, T_W, T_DistantMain, T_EM, T_ReEnforcedLocking};
	tp_Node = {T_RB, T_LB, T_P100, T_NI, T_P100A, T_P100B, T_NI2, T_NI1, T_NI4, T_NI3, T_NI6, T_NI5, T_NI7, T_P110, T_P110B, T_P110A};
	tp_Aspect = {T_SA_YY, T_SA_GOFF, T_SA_FYY, T_SA_POSA, T_SA_S, T_SA_MR, T_SA_R, T_SA_Y, T_SA_G, T_SA_OFF, T_SA_ON, T_SA_FY};
	tp_Direction = {T_Left, T_Right};
	tp_NIL = {T_nil};
	tp_Interlocking = {T_ixl_main};
	tp_Signal = {T_S100, T_S101, T_S108, T_S106, T_S104, T_S105, T_S102, T_S103, T_S110};
	tp_SubRouteOrientation = {T_AB, T_AC, T_AD, T_BA, T_BC, T_BD, T_CA, T_CB, T_DA, T_DB};
	tp_RouteDestination = {T_RDS_C, T_RDS_B, T_RDS_A, T_RDS_G, T_RDS_F, T_RDS_E, T_RDS_D, T_RDS_K, T_RDS_J, T_RDS_I, T_RDS_H};
	tp_Route = {T_R106_M_, T_R103_M_, T_R101_2_M_, T_R108B_M_, T_R102A_M_, T_R101_1_M_, T_R108A_M_, T_R100_M_, T_R102B_M_};
	tp_Track = {T_TAB, T_TAA, T_TAD, T_TAC, T_TAF, T_TBA, T_TBC, T_TBB}
CONCRETE_CONSTANTS
	id_route_normalpoints,
	id_subroute_path,
	id_SubRoute_derived,
	id_subroute_len,
	id_point_merged,
	id_subroute_from,
	id_subroute_direction,
	id_Route_class,
	id_route_entry,
	id_route_trackset,
	id_track_next,
	id_signal_type,
	id_Route_derived,
	id_track_ixl,
	id_subroute_opposite,
	id_route_subroutes,
	id_subroute_to,
	id_subroute_pointnormal,
	id_Track_derived,
	id_route_first,
	id_Node_base,
	id_route_subrouteset,
	id_track_circuit,
	id_subroute_pointreverse,
	id_signal_track,
	id_signal_aspects,
	id_safecap_route_derived_route_tracks,
	id_route_direction,
	id_subroute_next,
	id_signal_direction,
	id_point_tracks,
	id_subroute_track,
	id_point_direction,
	id_route_reversepoints,
	id_route_exit,
	id_Signal_derived,
	id_signal_joint,
	id_signal_offset,
	id_route_last,
	id_ixl_ambits
PROPERTIES
	id_route_normalpoints = {(T_R102B_M_ |-> T_P100A), (T_R102B_M_ |-> T_P110A), (T_R102A_M_ |-> T_P110B), (T_R101_1_M_ |-> T_P110A), (T_R101_1_M_ |-> T_P100A), (T_R108A_M_ |-> T_P100B), (T_R108A_M_ |-> T_P110B), (T_R108B_M_ |-> T_P100B) } &
	id_subroute_path = {(T_UAB_AB |-> T_AB), (T_UAA_AB |-> T_AB), (T_UAC_AC |-> T_AC), (T_UAB_BA |-> T_BA), (T_UAC_BC |-> T_BC), (T_UAD_BD |-> T_BD), (T_UAD_BC |-> T_BC), (T_UAC_CB |-> T_CB), (T_UAC_CA |-> T_CA), (T_UAD_CB |-> T_CB), (T_UAC_DA |-> T_DA), (T_UAD_DB |-> T_DB), (T_UAD_DA |-> T_DA), (T_UAF_BA |-> T_BA), (T_UBB_BA |-> T_BA) } &
	id_SubRoute_derived = {(T_UAB_AB |-> T_nil), (T_UAC_AC |-> T_nil), (T_UAA_AB |-> T_nil), (T_UAD_BD |-> T_nil), (T_UAB_BA |-> T_nil), (T_UAC_BC |-> T_nil), (T_UAD_BC |-> T_nil), (T_UAC_CB |-> T_nil), (T_UAD_CB |-> T_nil), (T_UAC_CA |-> T_nil), (T_UAC_DA |-> T_nil), (T_UAD_DB |-> T_nil), (T_UAD_DA |-> T_nil), (T_UAF_BA |-> T_nil), (T_UBB_BA |-> T_nil) } &
	id_subroute_len = {(T_UAB_AB |-> 12), (T_UAA_AB |-> 12), (T_UAC_AC |-> 137), (T_UAB_BA |-> 12), (T_UAC_BC |-> 37), (T_UAD_BD |-> 124), (T_UAD_BC |-> 24), (T_UAC_CB |-> 37), (T_UAC_CA |-> 137), (T_UAD_CB |-> 24), (T_UAC_DA |-> 37), (T_UAD_DB |-> 124), (T_UAD_DA |-> 24), (T_UAF_BA |-> 12), (T_UBB_BA |-> 12) } &
	id_point_merged = {(T_P100 |-> T_P100B), (T_P100 |-> T_P100A), (T_P110 |-> T_P110B), (T_P110 |-> T_P110A) } &
	id_subroute_from = {(T_UAB_AB |-> T_NI3), (T_UAA_AB |-> T_NI5), (T_UAC_AC |-> T_NI), (T_UAB_BA |-> T_NI5), (T_UAC_BC |-> T_NI1), (T_UAD_BD |-> T_NI7), (T_UAD_BC |-> T_NI7), (T_UAC_CB |-> T_NI3), (T_UAC_CA |-> T_NI3), (T_UAD_CB |-> T_NI1), (T_UAC_DA |-> T_NI2), (T_UAD_DB |-> T_NI), (T_UAD_DA |-> T_NI), (T_UAF_BA |-> T_NI7), (T_UBB_BA |-> T_NI4) } &
	id_subroute_direction = {(T_UAB_AB |-> T_Right), (T_UAA_AB |-> T_Right), (T_UAC_AC |-> T_Right), (T_UAB_BA |-> T_Left), (T_UAC_BC |-> T_Right), (T_UAD_BD |-> T_Right), (T_UAD_BC |-> T_Right), (T_UAC_CB |-> T_Left), (T_UAC_CA |-> T_Left), (T_UAD_CB |-> T_Left), (T_UAC_DA |-> T_Left), (T_UAD_DB |-> T_Left), (T_UAD_DA |-> T_Left), (T_UAF_BA |-> T_Left), (T_UBB_BA |-> T_Left) } &
	id_Route_class = {(T_R101_2_M_ |-> T_M), (T_R100_M_ |-> T_M), (T_R106_M_ |-> T_M), (T_R108A_M_ |-> T_M), (T_R108B_M_ |-> T_M), (T_R102B_M_ |-> T_M), (T_R103_M_ |-> T_M), (T_R102A_M_ |-> T_M), (T_R101_1_M_ |-> T_M) } &
	id_route_entry = {(T_R101_2_M_ |-> T_S101), (T_R100_M_ |-> T_S100), (T_R106_M_ |-> T_S106), (T_R108A_M_ |-> T_S108), (T_R108B_M_ |-> T_S108), (T_R102B_M_ |-> T_S102), (T_R103_M_ |-> T_S103), (T_R102A_M_ |-> T_S102), (T_R101_1_M_ |-> T_S101) } &
	id_route_trackset = {(T_R101_2_M_ |-> T_TAD), (T_R101_2_M_ |-> T_TAC), (T_R101_2_M_ |-> T_TAB), (T_R100_M_ |-> T_TAB), (T_R106_M_ |-> T_TBB), (T_R108A_M_ |-> T_TAC), (T_R108A_M_ |-> T_TAD), (T_R108B_M_ |-> T_TAC), (T_R108B_M_ |-> T_TAD), (T_R108B_M_ |-> T_TAF), (T_R102B_M_ |-> T_TAC), (T_R102B_M_ |-> T_TAD), (T_R102B_M_ |-> T_TAF), (T_R103_M_ |-> T_TAA), (T_R102A_M_ |-> T_TAC), (T_R102A_M_ |-> T_TAD), (T_R101_1_M_ |-> T_TAD), (T_R101_1_M_ |-> T_TAC), (T_R101_1_M_ |-> T_TAB) } &
	id_track_next = {(T_TBA |-> T_TBB), (T_TAB |-> T_TAC), (T_TAA |-> T_TAB), (T_TBB |-> T_TAC), (T_TAD |-> T_TAF), (T_TAD |-> T_TBC), (T_TAC |-> T_TAD), (T_TAC |-> T_TAD) } &
	id_signal_type = {(T_S108 |-> T_ST_Controlled), (T_S106 |-> T_ST_Controlled), (T_S104 |-> T_ST_Controlled), (T_S105 |-> T_ST_Controlled), (T_S102 |-> T_ST_Controlled), (T_S103 |-> T_ST_Controlled), (T_S100 |-> T_ST_Controlled), (T_S101 |-> T_ST_Controlled), (T_S110 |-> T_ST_Controlled) } &
	id_Route_derived = {(T_R101_2_M_ |-> T_nil), (T_R100_M_ |-> T_nil), (T_R106_M_ |-> T_nil), (T_R108A_M_ |-> T_nil), (T_R108B_M_ |-> T_nil), (T_R102B_M_ |-> T_nil), (T_R103_M_ |-> T_nil), (T_R102A_M_ |-> T_nil), (T_R101_1_M_ |-> T_nil) } &
	id_track_ixl = {(T_TBA |-> T_ixl_main), (T_TAB |-> T_ixl_main), (T_TBC |-> T_ixl_main), (T_TAA |-> T_ixl_main), (T_TBB |-> T_ixl_main), (T_TAD |-> T_ixl_main), (T_TAC |-> T_ixl_main), (T_TAF |-> T_ixl_main) } &
	id_subroute_opposite = {(T_AB |-> T_BA), (T_BC |-> T_CB), (T_AC |-> T_CA), (T_BD |-> T_DB), (T_AD |-> T_DA), (T_DA |-> T_AD), (T_CA |-> T_AC), (T_DB |-> T_BD), (T_BA |-> T_AB), (T_CB |-> T_BC) } &
	id_route_subroutes = {(T_R101_2_M_ |-> {(0, T_UAD_BD), (1, T_UAC_AC), (2, T_UAB_AB)}), (T_R100_M_ |-> {(0, T_UAB_BA)}), (T_R106_M_ |-> {(0, T_UBB_BA)}), (T_R108A_M_ |-> {(0, T_UAC_DA), (1, T_UAD_DA)}), (T_R108B_M_ |-> {(0, T_UAC_DA), (1, T_UAD_DB), (2, T_UAF_BA)}), (T_R102B_M_ |-> {(0, T_UAC_CB), (1, T_UAD_CB), (2, T_UAF_BA)}), (T_R103_M_ |-> {(0, T_UAA_AB)}), (T_R102A_M_ |-> {(0, T_UAC_CA), (1, T_UAD_DA)}), (T_R101_1_M_ |-> {(0, T_UAD_BC), (1, T_UAC_BC), (2, T_UAB_AB)}) } &
	id_subroute_to = {(T_UAB_AB |-> T_NI5), (T_UAA_AB |-> T_LB), (T_UAC_AC |-> T_NI3), (T_UAB_BA |-> T_NI3), (T_UAC_BC |-> T_NI3), (T_UAD_BD |-> T_NI), (T_UAD_BC |-> T_NI1), (T_UAC_CB |-> T_NI1), (T_UAC_CA |-> T_NI), (T_UAD_CB |-> T_NI7), (T_UAC_DA |-> T_NI), (T_UAD_DB |-> T_NI7), (T_UAD_DA |-> T_NI6), (T_UAF_BA |-> T_RB), (T_UBB_BA |-> T_NI2) } &
	id_subroute_pointnormal = {(T_UAC_BC |-> T_P100A), (T_UAD_BC |-> T_P110A), (T_UAC_CB |-> T_P100A), (T_UAD_CB |-> T_P110A), (T_UAC_DA |-> T_P100B), (T_UAD_DA |-> T_P110B) } &
	id_Track_derived = {(T_TBA |-> T_nil), (T_TAB |-> T_nil), (T_TBC |-> T_nil), (T_TBB |-> T_nil), (T_TAA |-> T_nil), (T_TAD |-> T_nil), (T_TAC |-> T_nil), (T_TAF |-> T_nil) } &
	id_route_first = {(T_R101_2_M_ |-> T_TAD), (T_R100_M_ |-> T_TAB), (T_R106_M_ |-> T_TBB), (T_R108A_M_ |-> T_TAC), (T_R108B_M_ |-> T_TAC), (T_R102B_M_ |-> T_TAC), (T_R103_M_ |-> T_TAA), (T_R102A_M_ |-> T_TAC), (T_R101_1_M_ |-> T_TAD) } &
	id_Node_base = {(T_P100 |-> T_P100), (T_P110B |-> T_P110), (T_P110 |-> T_P110), (T_P100A |-> T_P100), (T_P110A |-> T_P110), (T_P100B |-> T_P100) } &
	id_route_subrouteset = {(T_R101_2_M_ |-> T_UAD_BD), (T_R101_2_M_ |-> T_UAC_AC), (T_R101_2_M_ |-> T_UAB_AB), (T_R100_M_ |-> T_UAB_BA), (T_R106_M_ |-> T_UBB_BA), (T_R108A_M_ |-> T_UAC_DA), (T_R108A_M_ |-> T_UAD_DA), (T_R108B_M_ |-> T_UAC_DA), (T_R108B_M_ |-> T_UAD_DB), (T_R108B_M_ |-> T_UAF_BA), (T_R102B_M_ |-> T_UAC_CB), (T_R102B_M_ |-> T_UAD_CB), (T_R102B_M_ |-> T_UAF_BA), (T_R103_M_ |-> T_UAA_AB), (T_R102A_M_ |-> T_UAC_CA), (T_R102A_M_ |-> T_UAD_DA), (T_R101_1_M_ |-> T_UAD_BC), (T_R101_1_M_ |-> T_UAC_BC), (T_R101_1_M_ |-> T_UAB_AB) } &
	id_track_circuit = {(T_TBA |-> TRUE), (T_TAB |-> TRUE), (T_TBC |-> TRUE), (T_TAA |-> TRUE), (T_TBB |-> TRUE), (T_TAD |-> TRUE), (T_TAC |-> TRUE), (T_TAF |-> TRUE) } &
	id_subroute_pointreverse = {(T_UAD_BD |-> T_P110A), (T_UAD_BD |-> T_P110B), (T_UAC_CA |-> T_P100A), (T_UAC_CA |-> T_P100B), (T_UAD_DB |-> T_P110B), (T_UAD_DB |-> T_P110A), (T_UAC_AC |-> T_P100B), (T_UAC_AC |-> T_P100A) } &
	id_signal_track = {(T_S108 |-> T_TBB), (T_S106 |-> T_TBA), (T_S104 |-> T_TAF), (T_S105 |-> T_TAA), (T_S102 |-> T_TAB), (T_S103 |-> T_TAB), (T_S100 |-> T_TAA), (T_S101 |-> T_TAF), (T_S110 |-> T_TAD) } &
	id_signal_aspects = {(T_S108 |-> T_SA_Y), (T_S108 |-> T_SA_G), (T_S108 |-> T_SA_R), (T_S106 |-> T_SA_Y), (T_S106 |-> T_SA_G), (T_S106 |-> T_SA_R), (T_S104 |-> T_SA_Y), (T_S104 |-> T_SA_G), (T_S104 |-> T_SA_R), (T_S105 |-> T_SA_Y), (T_S105 |-> T_SA_G), (T_S105 |-> T_SA_R), (T_S102 |-> T_SA_Y), (T_S102 |-> T_SA_G), (T_S102 |-> T_SA_R), (T_S103 |-> T_SA_Y), (T_S103 |-> T_SA_G), (T_S103 |-> T_SA_R), (T_S100 |-> T_SA_Y), (T_S100 |-> T_SA_G), (T_S100 |-> T_SA_R), (T_S101 |-> T_SA_Y), (T_S101 |-> T_SA_G), (T_S101 |-> T_SA_R), (T_S110 |-> T_SA_Y), (T_S110 |-> T_SA_G), (T_S110 |-> T_SA_R) } &
	id_safecap_route_derived_route_tracks = {(T_R101_2_M_ |-> (0, T_TAD)), (T_R101_2_M_ |-> (1, T_TAC)), (T_R101_2_M_ |-> (2, T_TAB)), (T_R100_M_ |-> (0, T_TAB)), (T_R106_M_ |-> (0, T_TBB)), (T_R108A_M_ |-> (0, T_TAC)), (T_R108A_M_ |-> (1, T_TAD)), (T_R108B_M_ |-> (0, T_TAC)), (T_R108B_M_ |-> (1, T_TAD)), (T_R108B_M_ |-> (2, T_TAF)), (T_R102B_M_ |-> (0, T_TAC)), (T_R102B_M_ |-> (1, T_TAD)), (T_R102B_M_ |-> (2, T_TAF)), (T_R103_M_ |-> (0, T_TAA)), (T_R102A_M_ |-> (0, T_TAC)), (T_R102A_M_ |-> (1, T_TAD)), (T_R101_1_M_ |-> (0, T_TAD)), (T_R101_1_M_ |-> (1, T_TAC)), (T_R101_1_M_ |-> (2, T_TAB)) } &
	id_route_direction = {(T_R101_2_M_ |-> T_Right), (T_R100_M_ |-> T_Left), (T_R106_M_ |-> T_Left), (T_R108A_M_ |-> T_Left), (T_R108B_M_ |-> T_Left), (T_R102B_M_ |-> T_Left), (T_R103_M_ |-> T_Right), (T_R102A_M_ |-> T_Left), (T_R101_1_M_ |-> T_Right) } &
	id_subroute_next = {(T_UAB_AB |-> T_UAA_AB), (T_UAC_AC |-> T_UAB_AB), (T_UAB_BA |-> T_UAC_CB), (T_UAB_BA |-> T_UAC_CA), (T_UAC_BC |-> T_UAB_AB), (T_UAD_BD |-> T_UAC_AC), (T_UAD_BC |-> T_UAC_BC), (T_UAC_CB |-> T_UAD_CB), (T_UAC_CA |-> T_UAD_DB), (T_UAC_CA |-> T_UAD_DA), (T_UAD_CB |-> T_UAF_BA), (T_UBB_BA |-> T_UAC_DA), (T_UAC_DA |-> T_UAD_DB), (T_UAC_DA |-> T_UAD_DA), (T_UAD_DB |-> T_UAF_BA) } &
	id_signal_direction = {(T_S108 |-> T_Left), (T_S106 |-> T_Left), (T_S104 |-> T_Left), (T_S105 |-> T_Right), (T_S102 |-> T_Left), (T_S103 |-> T_Right), (T_S100 |-> T_Left), (T_S101 |-> T_Right), (T_S110 |-> T_Left) } &
	id_point_tracks = {(T_P110B |-> T_TAD), (T_P100A |-> T_TAC), (T_P110A |-> T_TAD), (T_P100B |-> T_TAC) } &
	id_subroute_track = {(T_UAB_AB |-> T_TAB), (T_UAA_AB |-> T_TAA), (T_UAC_AC |-> T_TAC), (T_UAB_BA |-> T_TAB), (T_UAC_BC |-> T_TAC), (T_UAD_BD |-> T_TAD), (T_UAD_BC |-> T_TAD), (T_UAC_CB |-> T_TAC), (T_UAC_CA |-> T_TAC), (T_UAD_CB |-> T_TAD), (T_UAC_DA |-> T_TAC), (T_UAD_DB |-> T_TAD), (T_UAD_DA |-> T_TAD), (T_UAF_BA |-> T_TAF), (T_UBB_BA |-> T_TBB) } &
	id_point_direction = {(T_P110B |-> T_Right), (T_P100A |-> T_Right), (T_P110A |-> T_Left), (T_P100B |-> T_Left) } &
	id_route_reversepoints = {(T_R101_2_M_ |-> T_P110A), (T_R101_2_M_ |-> T_P110B), (T_R101_2_M_ |-> T_P100B), (T_R101_2_M_ |-> T_P100A), (T_R102A_M_ |-> T_P100A), (T_R102A_M_ |-> T_P100B), (T_R108B_M_ |-> T_P110B), (T_R108B_M_ |-> T_P110A) } &
	id_route_exit = {(T_R101_2_M_ |-> T_S103), (T_R100_M_ |-> T_S102), (T_R106_M_ |-> T_S108), (T_R108A_M_ |-> T_S110), (T_R108B_M_ |-> T_S104), (T_R102B_M_ |-> T_S104), (T_R103_M_ |-> T_S105), (T_R102A_M_ |-> T_S110), (T_R101_1_M_ |-> T_S103) } &
	id_Signal_derived = {(T_S108 |-> T_nil), (T_S106 |-> T_nil), (T_S104 |-> T_nil), (T_S105 |-> T_nil), (T_S102 |-> T_nil), (T_S103 |-> T_nil), (T_S100 |-> T_nil), (T_S101 |-> T_nil), (T_S110 |-> T_nil) } &
	id_signal_joint = {(T_S108 |-> T_NI2), (T_S106 |-> T_NI4), (T_S104 |-> T_RB), (T_S105 |-> T_LB), (T_S102 |-> T_NI3), (T_S103 |-> T_NI5), (T_S100 |-> T_NI5), (T_S101 |-> T_NI7), (T_S110 |-> T_NI6) } &
	id_signal_offset = {(T_S108 |-> 12), (T_S106 |-> 12), (T_S104 |-> 12), (T_S105 |-> 12), (T_S102 |-> 12), (T_S103 |-> 12), (T_S100 |-> 12), (T_S101 |-> 12), (T_S110 |-> 12) } &
	id_route_last = {(T_R101_2_M_ |-> T_TAB), (T_R100_M_ |-> T_TAB), (T_R106_M_ |-> T_TBB), (T_R108A_M_ |-> T_TAD), (T_R108B_M_ |-> T_TAF), (T_R102B_M_ |-> T_TAF), (T_R103_M_ |-> T_TAA), (T_R102A_M_ |-> T_TAD), (T_R101_1_M_ |-> T_TAB) } &
	id_ixl_ambits = {(T_ixl_main |-> T_TBA), (T_ixl_main |-> T_TAA), (T_ixl_main |-> T_TBB), (T_ixl_main |-> T_TAB), (T_ixl_main |-> T_TBC), (T_ixl_main |-> T_TAF), (T_ixl_main |-> T_TAC), (T_ixl_main |-> T_TAD) }
END
